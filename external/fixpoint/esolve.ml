(*
 * Copyright © 2009 The Regents of the University of California. All rights reserved. 
 *
 * Permission is hereby granted, without written agreement and without 
 * license or royalty fees, to use, copy, modify, and distribute this 
 * software and its documentation for any purpose, provided that the 
 * above copyright notice and the following two paragraphs appear in 
 * all copies of this software. 
 * 
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY 
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES 
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN 
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE. 
 * 
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, 
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS 
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION 
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *)


(** This module implements a fixpoint solver *)
module BS = BNstats
module F  = Format
module A  = Ast
module Co = Constants
module P  = A.Predicate
module E  = A.Expression
module So = A.Sort
module Su = A.Subst
module Q  = Qualifier
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint
module Ci = Cindex
module PP = Prepass
module Cg = FixConfig
module IMap = Map.Make(struct type t = int let compare = compare end)
(* module TP   = TpNull.Prover *)
module Misc = FixMisc open Misc.Ops



let mydebug  = false
let vmydebug = false

type t = {
   sri  : Ci.t
 ; ws   : C.wf list
 ; negs : Sy.t list
 ; tt   : Timer.t
   
 (* Stats *)
 ; stat_refines        : int ref
 ; stat_cfreqt         : (int * bool, int) Hashtbl.t 
}

module type SOLVER = sig
  type soln
  type bind
  val create    : bind Cg.cfg -> FixConstraint.psoln option -> (int * (int list)) -> (int * t * soln)
  val create_deps    : bind Cg.cfg -> FixConstraint.soln option -> (int * (int list)) list
  val solve     : (int * t * soln)  -> (soln * (FixConstraint.t list) * Counterexample.cex list)
  val save      : string -> t -> soln -> unit 
  val read      : soln -> FixConstraint.soln
  val min_read  : soln -> FixConstraint.soln
  val read_bind : soln -> Ast.Symbol.t -> bind
  val cone      : t -> FixConstraint.id -> FixConstraint.tag Ast.Cone.t
  (* val meet   : soln -> soln -> soln  *)
end

module Make (Dom : SolverArch.DOMAIN) = struct
  type soln     = Dom.t
  type bind     = Dom.bind
  let min_read  = Dom.min_read
  let read      = Dom.read
  let read_bind = Dom.read_bind  
(* let meet = Dom.meet *)


(*************************************************************)
(********************* Stats *********************************)
(*************************************************************)

let hashtbl_incr_frequency t k = 
  let n = try Hashtbl.find t k with Not_found -> 0 in
  Hashtbl.replace t k (n+1)

let hashtbl_print_frequency t = 
  Misc.hashtbl_to_list t 
  |> Misc.kgroupby (fun ((k,b),n) -> (n,b))
  |> List.map (fun ((n,b), xs) -> (n, b, List.map (fst <+> fst) xs))
  |> List.sort compare
  |> List.iter begin fun (n, b, xs) -> 
       Co.bprintf vmydebug "ITERFREQ: %d times (ch = %b) %d constraints %s \n"
         n b (List.length xs) (Misc.map_to_string string_of_int xs) 
     end

(***************************************************************)
(************************ Debugging/Stats **********************)
(***************************************************************)

let print_constr_stats ppf cs = 
  let cn   = List.length cs in
  let scn  = List.length (List.filter C.is_simple cs) in
  F.fprintf ppf "#Constraints: %d (simple = %d) \n" cn scn

let print_solver_stats ppf me = 
  print_constr_stats ppf (Ci.to_list me.sri); 
  F.fprintf ppf "#Iterations = %d\n" !(me.stat_refines);
  F.fprintf ppf "Iteration Frequency: \n"; 
    hashtbl_print_frequency me.stat_cfreqt;
  F.fprintf ppf "Iteration Periods: @[%a@] \n" Timer.print me.tt

let dump me s = 
  Co.bprintf mydebug "%a \n" print_solver_stats me;
  Co.bprintf mydebug "%a \n" Dom.print_stats s;
  Dom.dump s

let log_iter_stats me s =
  (if Co.ck_olev Co.ol_insane then Co.bprintf mydebug "log_iter_stats\n%a" Dom.print s);
  (if !(me.stat_refines) mod 100 = 0 then 
     let msg = Printf.sprintf "\n num refines=%d" !(me.stat_refines) in 
     let _   = Timer.log_event me.tt (Some msg)                      in
     let _   = Co.bprintf mydebug "%s\n %a\n" msg Dom.print_stats s  in
     let _   = Format.print_flush ()                                 in
     ());
  ()

(***************************************************************)
(******************** Lattice Construction *********************)
(***************************************************************)

let go_up qs old =
  let _   = Co.bprintflush mydebug "\nBEGIN: go_up \n" in
  let msg = F.sprintf "\n|QS| = %n  - |OLD| = %n \n" (Array.length qs) (List.length old) in
  let _   = Co.bprintflush mydebug msg in

  let f (x, is) = List.map (fun i -> 
    (Array.get qs i :: x, List.filter (fun x -> x != i) is)) is   in 
  old |> List.map f |> List.concat
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: go_up \n")


let is_min s ds = 
  let ds' = Dom.min_binds s ds in 
  List.length ds' == List.length ds

let make_lattice_one k sm s qs = 
  let _   = Co.bprintflush mydebug "\nBEGIN: make_lattice_one \n" in
  let msg = F.sprintf "\nfor %s|QS| = %n \n" (Sy.to_string k) (List.length qs) in
  let _   = Co.bprintflush mydebug msg in

  let (cqs, qs) = List.partition (Q.pred_of_t <+> P.is_contra) qs in
  let a = Array.of_list qs in
  let nq = List.length qs in
  let rec go n acc now = 
    match go_up a now with
      | []  -> acc
      | [(qss,[])] -> acc @ [qss]
      | [_] -> (assert false)
      | qss -> begin 
        let msg = F.sprintf "\nStart is simple |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in
        let qss = List.filter (fun (qs, _) -> is_min s qs) qss in
        let msg = F.sprintf "\nEnd is simple |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in
        

        let msg = F.sprintf "\nStart is contra |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in

        let qss = List.filter (fun (qs, _) -> not (Dom.is_contra sm s qs)) qss in
        let msg = F.sprintf "\nEnd is contra |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in
                 
        let is_implied qs = List.exists (fun ds -> Dom.is_equiv sm s qs ds) acc in 
        let msg = F.sprintf "\nStart is implied |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in
        let qss = List.filter (fun (qs, _) -> not (is_implied qs)) qss in
        let msg = F.sprintf "\nEnd is implied |qss| = %d\n" (List.length qss) in
        let _   = Co.bprintflush mydebug msg in
                 
        let _acc = List.split qss |> fst in 
        let __acc = acc @ _acc in
        go (n+1) __acc qss end
  in 
  let ns  = Misc.range 0 (nq-1) in
  let qss = List.map (fun x -> [x]) qs in
  let qns =
   a |> Array.mapi (fun i x -> ([x], Misc.range (i+1) (nq-1))) 
     |> Array.to_list in
  go 1 ([]::qss) qns
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: make_lattice_one \n")
 

let make_lattice ws s ps = 
  let _  = Co.bprintflush mydebug "\nBEGIN: make_lattice \n" in
  SM.mapi (fun k ds -> 
    let ws = List.filter 
      (fun w -> List.mem k 
       (List.map snd (C.kvars_of_reft (C.reft_of_wf w)))
      ) ws in
    let wf = match ws with 
             | [wf] -> wf
             | _ -> (assert false) [] in
    ds |>
    let sm = SM.map (fun (_, x, _) -> x) (C.env_of_wf wf) in 
    make_lattice_one k sm s <+> Array.of_list) ps
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: make_lattice \n")

let _init_soln ltc =
  let _  = Co.bprintflush mydebug "\nBEGIN: _init_soln \n" in
  let ltc = ltc |> SM.bindings 
      |> List.map (fun (k, x) -> ((0, Array.length x), (k, x))) 
      |> Array.of_list in 
  (((Array.length ltc)-1,Array.length ltc), ltc)
  >> fun _ ->  Co.bprintflush mydebug "\nDONE: _init_soln \n"

let init_soln me s p = 
  p |> make_lattice me.ws s |> _init_soln

let soln_to_map ((i,n),a) =
   a  |> Array.to_list 
      |> List.map (fun ((i,_),(k,aa)) -> (k, Array.get aa i)) 
      |> SM.of_list 

let next_element ((i, n), a) =
  let _ = Co.bprintflush mydebug "\nBEGIN: next_element\n" in 
  if n > 0 then (
    let rec go ii aa = 
      let ((j,jj), aii) = Array.get aa ii in 
       if (ii == 0 && j == jj-1) 
       then None
       else if (j == jj-1) 
       then (Array.set aa ii ((0,jj),aii); go (ii-1) aa)
       else (Array.set aa ii ((j+1,jj),aii); Some ((i,n),aa))
    in  match go (n-1) a with 
        | Some ((ii,nn),aa) -> (
          let _ = F.printf "\n" in
          let _ = Array.mapi (fun i ((j,m), _) -> F.printf "\t(%d,%d)" j m) a in
          (Some ((ii,nn), aa)))
       | None -> None 
  ) else None 
  >> (fun _ ->  Co.bprintflush mydebug "\nEND: next_element\n")

let is_solved s c = 
  let sol = read s in
  c |> C.rhs_of_t 
    |> C.kvars_of_reft
    |> List.map (sol <.> snd)
    |> List.for_all ((=) [])

(***************************************************************)
(******************** Iterative Refinement *********************)
(***************************************************************)

let refine_constraint s c =
  try BS.time "refine" (Dom.refine s) c with ex ->
    let _ = F.printf "constraint refinement fails with: %s\n" (Printexc.to_string ex) in
    let _ = F.printf "Failed on constraint:\n%a\n" (C.print_t None) c in
    assert false

let update_worklist me s' c w' = 
  c |> Ci.deps me.sri 
    |> Misc.filter (not <.> is_solved s')
    |> Ci.wpush me.sri w'

let rec acsolve me w s =
  let _ = if vmydebug then log_iter_stats me s else () in
  let _ = if vmydebug then Misc.display_tick () else () in
  match Ci.wpop me.sri w with 
  | (None,_) -> 
      let _ = Timer.log_event me.tt (Some "Finished") in 
      s 
  | (Some c, w') ->
      let _        = me.stat_refines += 1             in 
      let (ch, s') = BS.time "refine" (refine_constraint s) c in
      let _        = hashtbl_incr_frequency me.stat_cfreqt (C.id_of_t c, ch) in  
      let _        = Co.bprintf vmydebug "iter=%d id=%d ch=%b %a \n" 
                      !(me.stat_refines) (C.id_of_t c) ch C.print_tag (C.tag_of_t c) in
      let w''      = if ch then update_worklist me s' c w' else w' in 
      acsolve me w'' s' 

let unsat_constraints me s =
  me.sri |> Ci.to_list |> List.filter (Dom.unsat s)

let simplify_solution me s = Dom.simplify s


(***************************************************************)
(****************** Pruning Unconstrained Vars *****************)
(***************************************************************)

let rhs_ks cs =
  cs  |> Misc.flap (Misc.compose C.kvars_of_reft C.rhs_of_t)
      |> List.fold_left (fun rhss (_, kv) -> Sy.SSet.add kv rhss) Sy.SSet.empty

let lhs_ks cs =
  cs  |> Misc.flap (Misc.compose C.kvars_of_reft C.lhs_of_t)
      |> List.fold_left (fun lhss (_, kv) -> Sy.SSet.add kv lhss) Sy.SSet.empty

let envs_ks cs =
  cs  |> Misc.flap (Misc.compose C.kvars_of_env C.env_of_t)
      |> List.fold_left (fun lhss (_, kv) -> Sy.SSet.add kv lhss) Sy.SSet.empty

let unconstrained_kvars cs =
  let rhss = rhs_ks cs in
  cs  |> Misc.flap C.kvars_of_t
      |> List.map snd
      |> List.filter (fun kv -> not (Sy.SSet.mem kv rhss))

let true_unconstrained sri s =
  sri |> Ci.to_list 
      |> unconstrained_kvars
      |> Dom.top s

let neg_unconstrained_kvars cs =
  let lhss = lhs_ks cs in
  let envss = envs_ks cs in
  let kss =  Sy.SSet.union lhss envss in
  cs  |> Misc.flap C.kvars_of_t
      |> List.map snd
      |> List.filter (fun kv -> not (Sy.SSet.mem kv kss))

let neg_true_unconstrained sri =
  neg_unconstrained_kvars (Ci.to_list sri) |> Sy.SSet.of_list

let print_p p 
 = 
   F.printf "\nBEGIN P"; 
   SM.mapi begin  
     fun k ds -> F.printf "\n(S = %d) %s = %a" 
     (List.length ds) (Sy.to_string k)
     (Misc.pprint_many false ", " Q.print_pred) ds
   end p;
   F.printf "\nEND P\n" 

let nq = ref 0    

let create_q template pred = 
    let qname = incr nq; Sy.of_string 
    (String.concat "" ["DummyQ";(string_of_int !nq)]) in
    let qvar  = Q.vv_of_t template in 
    let qsort = Q.sort_of_t template in 
    Q.create qname qvar qsort [] pred 

let group lss = 
    let rec go acc = function
      | [] -> acc
      | (([])::lss) -> go acc lss
      | (((x,y)::ls)::lss) -> 
        if List.mem_assoc x acc
        then let ys = List.assoc x acc in 
             let _acc = List.remove_assoc x acc in
             go ((x,(y::ys))::_acc) (ls::lss)
        else go ((x,[y])::acc) (ls :: lss)
    in go [] lss 

let mapSnd f (x, y) = (x, f y)

let union_one dss =  
     match List.concat (List.map fst dss) with 
      | [] -> []
      | (d::_) -> (
        let f (ds,epds) =
         let pds = List.map Q.pred_of_t ds in pds@epds
        in           
        let pd =  dss |> List.map (f <+> Ast.pAnd)
              |> Ast.pOr in  
        let qq = create_q d pd in [qq]
      )
(*UP TO HERE *)
let punion me sups = 
  let g p = 
    SM.mapi begin fun k ds -> 
      let w = match List.filter begin fun w -> 
        List.mem k (List.map snd (C.kvars_of_reft (C.reft_of_wf w)))
         end me.ws with 
       |[w] -> w
       | _ -> assert false
      in
      let suu k = if SM.mem k p
            then SM.find k p |>: Q.pred_of_t |> fun x -> x
            else [] in

      let env  = C.env_of_wf w in
      let epds = SM.mapi begin fun i (v,s,rs) ->
            let _rs = List.filter begin fun r -> 
            match r with 
            | C.Kvar _ -> true
            | C.Conc _ -> false
      end rs in
            let pds = C.preds_of_reft suu (v,s,_rs) in 
             List.map begin fun p -> 
               Ast.Predicate.subst p v (Ast.eVar i) end  pds
         end env
      in 
      let epds = 
           epds |> SM.bindings |> List.map snd |> List.concat in
      (ds, epds) end p 
  in 
  sups |> List.map snd
       |> List.map g
       |> List.map SM.bindings
       |> group 
       |> List.map (mapSnd union_one) 
       |> SM.of_list


let rec loop i s acc me pm sinit =

    let p = soln_to_map pm in

    let _ = F.printf "\nCURRENT = " in 
    let _ = print_p p in 
    let _ = F.printf "\nBEGIN ACCUM = " in 
    let _ = List.map (snd <+> print_p) acc in 
    let _ = F.printf "END ACCUM\n" in 

    let empty_acc = match acc with | [] -> true | _ -> false in 

    let suu k = if SM.mem k p
               then SM.find k p |>: Q.pred_of_t |> fun x -> x
               else [] in

    let negws = 
    List.filter 
    (fun w -> List.exists (fun k -> List.mem k me.negs) 
       (List.map snd (C.kvars_of_reft (C.reft_of_wf w)))
    ) 
    me.ws in


    let is_contra_wf w = 
      let env  = C.env_of_wf w in
      let (wv,ws,wr)  = C.reft_of_wf w in
      let refts = SM.mapi 
      (fun i (v,s,rs) -> let pds = C.preds_of_reft suu (v,s,rs) in 
                         List.map (fun p -> Ast.Predicate.subst p v (Ast.eVar i)) pds
      ) 
      env 
      |> SM.to_list |> List.map snd
      in
      let syms = SM.add wv ws (SM.map (fun (_,s,_) -> s) env)  in
      let pds = (C.preds_of_reft suu (C.reft_of_wf w)) @ 
            List.concat refts in 
      Dom.is_contra_pred syms s pds
    in

    let is_implied_wf new_solution old_solution w =

    let pnew = new_solution in
    let suu k = if SM.mem k pnew
              then SM.find k pnew |>: Q.pred_of_t |> fun x -> x
               else [] in

    
    let pold = old_solution in 
    let suuold k = if SM.mem k pold
                   then SM.find k pold |>: Q.pred_of_t |> fun x -> x
                   else [] in 
   
      let env = C.env_of_wf w in 
      let (wv,ws,wr)  = C.reft_of_wf w in
      let _ = F.printf "\nStart is implied for %s\n" 
        (String.concat " , " 
        (List.map (snd <+>Sy.to_string) (C.kvars_of_reft (wv,ws,wr))))
      in
      let refts = SM.mapi 
      (fun i (v,s,rs) -> let pds = C.preds_of_reft suu (v,s,rs) in 
                         List.map (fun p -> Ast.Predicate.subst p v (Ast.eVar i)) pds
      ) 
      env 
      |> SM.to_list |> List.map snd
      in
      let syms = SM.add wv ws (SM.map (fun (_,s,_) -> s) env)  in
      let pnew = (C.preds_of_reft suu (C.reft_of_wf w)) @ 
            List.concat refts |> Ast.pAnd in
      let pold = (C.preds_of_reft suuold (C.reft_of_wf w)) @ 
            List.concat refts |> Ast.pAnd in
      Dom.is_contra_pred syms s [(Ast.pNot (Ast.pImp(pnew, pold)))]
      >> (fun b -> F.printf "\nEnd is implied = %s\n" (if b then "true" else "false") ; b)

      in

    if List.exists is_contra_wf negws || 
       List.exists (fun s -> List.for_all (is_implied_wf p (snd s)) negws) acc  then 
    match next_element pm with
                | None -> acc
                | Some pm' -> 
                  (loop (i+1) s acc me pm'
                sinit)

      else (  

(* BEGIN LOOP *)
    let su k = if SM.mem k p
               then SM.find k p |>: Q.pred_of_t |> fun x -> Some x
               else None in
    let _me    = {me with sri = Ci.wapply_psoln su me.sri} in

    let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Initialize Worklist \n" in
    let w  = BS.time "Cindex.winit" Ci.winit _me.sri in 
    let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Initialize Worklist \n" in
 
    let _  = Co.bprintflush vmydebug "\nBEGIN: Fixpoint Refinement Loop \n" in
    let si  = BS.time "Solve.acsolve"  (acsolve _me w) sinit in
    let _  = Co.bprintflush vmydebug "\nDONE: Fixpoint Refinement Loop \n" in
  (* let _ = F.printf "create: SOLUTION2 \n %a \n" Dom.print s in *)
    let _  = Co.bprintflush vmydebug "\nBEGIN: Simplify Solution \n" in
    let s  = if !Co.minquals then simplify_solution _me si else si in
    let _  = Co.bprintflush vmydebug "\nDONE: Simplify Solution \n" in
    let _  = if vmydebug then BS.time "Solve.dump" (dump _me) s else ()  in
    let _  = Co.bprintflush mydebug "Fixpoint: Testing Solution \n" in
    let u  = BS.time "Solve.unsatcs" (unsat_constraints _me) si in
    let unsafe _ = 
      if vmydebug 
      then F.printf "Unsatisfied Constraints:\n %a" 
        (Misc.pprint_many true "\n" (C.print_t None)) u 
      else () in
    let acc = if u == [] 
              then (
                
                let newacc = (List.filter begin 
                fun (sold, pold) ->
                  List.exists begin fun w -> 
                    not (is_implied_wf pold p w)
                  end negws
                end acc ) in
                    
                if List.length newacc < List.length acc then 
                  F.printf "\nSHRINK!\n" else ();  
                (s,p) :: newacc    
                    )  
              else (unsafe (); acc) in
    match next_element pm with
                | None -> acc
                | Some pm' ->  loop (i+1) s acc me pm' sinit

      )


let is_contra_wf s solution w =
    let suu k = if SM.mem k solution
              then SM.find k solution |>: Q.pred_of_t |> fun x -> x
               else [] in
      let env  = C.env_of_wf w in
      let (wv,ws,wr)  = C.reft_of_wf w in
      let refts = SM.mapi 
      (fun i (v,s,rs) -> let pds = C.preds_of_reft suu (v,s,rs) in 
                         List.map (fun p -> Ast.Predicate.subst p v (Ast.eVar i)) pds
      ) 
      env 
      |> SM.to_list |> List.map snd
      in
      let syms = SM.add wv ws (SM.map (fun (_,s,_) -> s) env)  in
      let pds = (C.preds_of_reft suu (C.reft_of_wf w)) @ 
            List.concat refts in 
      Dom.is_contra_pred syms s pds

let is_implied_wf s new_solution old_solution w =

    let pnew = new_solution in
    let suu k = if SM.mem k pnew
              then SM.find k pnew |>: Q.pred_of_t |> fun x -> x
               else [] in

    
    let pold = old_solution in 
    let suuold k = if SM.mem k pold
                   then SM.find k pold |>: Q.pred_of_t |> fun x -> x
                   else [] in 
   
      let env = C.env_of_wf w in 
      let (wv,ws,wr)  = C.reft_of_wf w in
      let _ = F.printf "\nStart is implied for %s\n" 
        (String.concat " , " 
        (List.map (snd <+>Sy.to_string) (C.kvars_of_reft (wv,ws,wr))))
      in
      let refts = SM.mapi 
      (fun i (v,s,rs) -> let pds = C.preds_of_reft suuold (v,s,rs) in 
                         List.map (fun p -> Ast.Predicate.subst p v (Ast.eVar i)) pds
      ) 
      env 
      |> SM.to_list |> List.map snd
      in
      let syms = SM.add wv ws (SM.map (fun (_,s,_) -> s) env)  in
      let pnew = (C.preds_of_reft suu (C.reft_of_wf w)) @ 
            List.concat refts |> Ast.pAnd in
      let pold = (C.preds_of_reft suuold (C.reft_of_wf w)) @ 
            List.concat refts |> Ast.pAnd in
      Dom.is_contra_pred syms s [(Ast.pNot (Ast.pImp(pnew, pold)))]
      >> (fun b -> F.printf "\nEnd is implied = %s for %a \n\n" (if b then
        "true" else "false")  Ast.Predicate.print 
        (Ast.pNot (Ast.pImp (pnew, pold)) ) ; b)
(* TO HERE *)
let solve_one me s = 
  let _  = Co.bprintflush mydebug "Fixpoint: Validating Initial Solution \n" in
  let _  = BS.time "Prepass.profile" PP.profile me.sri in
  let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Trueing Unconstrained Variables \n" in
  let s  = s |> (!Co.true_unconstrained <?> BS.time "Prepass.true_unconstr" (true_unconstrained me.sri)) in
  let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Trueing Unconstrained Variables \n" in

  
  let (p0, sinit) = Dom.drop s me.negs in
  let puks = neg_true_unconstrained me.sri in
  let p0 = SM.filter (fun k _ -> not (Sy.SSet.mem k puks) ) p0 in

  (* BEGIN : testing true solution *)
  let sinit = Dom.add sinit 
    (Sy.SSet.elements puks |> List.map (fun x -> (x, []))
                           |> SM.of_list) in 
  
  let pempty = SM.map (fun _ -> [] ) p0 in 
  
  let sue k = if SM.mem k pempty
               then Some [Ast.pTrue] 
               else None in
  let mee   = {me with sri = Ci.wapply_psoln sue me.sri} in

  let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Initialize Worklist \n" in
  let we  = BS.time "Cindex.winit" Ci.winit mee.sri in 
  let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Initialize Worklist \n" in
 
  let _  = Co.bprintflush vmydebug "\nBEGIN: Fixpoint Refinement Loop \n" in
  let sie  = BS.time "Solve.acsolve"  (acsolve mee we) sinit in
  let _  = Co.bprintflush vmydebug "\nDONE: Fixpoint Refinement Loop \n" in
  let _  = Co.bprintflush vmydebug "\nBEGIN: Simplify Solution \n" in
  let se  = if !Co.minquals then simplify_solution mee sie else sie in
  let _  = Co.bprintflush vmydebug "\nDONE: Simplify Solution \n" in
  let _  = if vmydebug then BS.time "Solve.dump" (dump mee) s else ()  in
  let _  = Co.bprintflush mydebug "Fixpoint: Testing Solution \n" in
  let ue  = BS.time "Solve.unsatcs" (unsat_constraints mee) sie in
  (* DONE : testing true solution *)
  if (ue == []) then 
    (Dom.add se pempty, [], [])
  else ( 
    let p = p0 in
  
    let _  = Co.bprintflush mydebug "\nBEGIN: Exhaustive: Call init_soln \n" in
    let pm = init_soln me s p in
    let _  = Co.bprintflush mydebug "\nDONE: Exhaustive: Call init_soln \n" in
  
    let sups = loop 0 s [] me pm sinit in
  
    let f s u = if !Co.cex && Misc.nonnull u then Dom.ctr_examples s (Ci.to_list me.sri) u else [] in
    let sup = List.map (fun (s, p) -> (Dom.add s p, [], [])) sups in 
    let p_union = punion me sups in  
  (*BEGIN : SOLVE WITH UNION *)
    let p = p_union in 
    let su k = if SM.mem k p
                 then SM.find k p |>: Q.pred_of_t |> fun x -> Some x
                 else None in
    let _me    = {me with sri = Ci.wapply_psoln su me.sri} in
  
    let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Initialize Worklist \n" in
    let w  = BS.time "Cindex.winit" Ci.winit _me.sri in 
    let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Initialize Worklist \n" in
   
    let _  = Co.bprintflush vmydebug "\nBEGIN: Fixpoint Refinement Loop \n" in
   let si  = BS.time "Solve.acsolve"  (acsolve _me w) sinit in
   let _  = Co.bprintflush vmydebug "\nDONE: Fixpoint Refinement Loop \n" in
    (* let _ = F.printf "create: SOLUTION2 \n %a \n" Dom.print s in *)
   let _  = Co.bprintflush vmydebug "\nBEGIN: Simplify Solution \n" in
   let s  = if !Co.minquals then simplify_solution _me si else si in
   let _  = Co.bprintflush vmydebug "\nDONE: Simplify Solution \n" in
   let _  = if vmydebug then BS.time "Solve.dump" (dump _me) s else ()  in
   let _  = Co.bprintflush mydebug "Fixpoint: Testing Solution \n" in
   let u  = BS.time "Solve.unsatcs" (unsat_constraints _me) si in
  (*END : SOLVE WITH UNION *)
   (Dom.add s p, u, [])
)

(* API *)
let solve (i,me,s) = solve_one me s 

let global_symbols cfg = 
     (SM.to_list cfg.Cg.uops)   (* specified globals *) 
  ++ (Theories.interp_syms)     (* theory globals    *)

(* API *)
let create_one cfg kf =
  let gts = global_symbols cfg in
  let sri = cfg.Cg.cs
            >> Co.bprintf mydebug "Pre-Simplify Stats\n%a" print_constr_stats
            |> BS.time  "Constant Env" (List.map (C.add_consts_t gts))
            |> BS.time  "Simplify" FixSimplify.simplify_ts
            >> Co.bprintf mydebug "Post-Simplify Stats\n%a" print_constr_stats
            |> BS.time  "Ref Index" Ci.create cfg.Cg.kuts cfg.Cg.ds
            |> (!Co.slice <?> BS.time "Slice" Ci.slice) in
  let ws  = cfg.Cg.ws
            |> (!Co.slice <?> BS.time "slice_wf" (Ci.slice_wf sri))
            |> BS.time  "Constant EnvWF" (List.map (C.add_consts_wf gts))
            |> PP.validate_wfs in
  let cfg = { cfg with Cg.cs = Ci.to_list sri; Cg.ws = ws } in
  let s   = if !Constants.dump_simp <> "" then Dom.empty else BS.time "Dom.create" (Dom.create cfg) kf in
  let _   = Co.bprintflush mydebug "\nDONE: Dom.create\n" in
  let _   = Co.bprintflush mydebug "\nBEGIN: PP.validate\n" in
  let _   = Ci.to_list sri
            |> BS.time "Validate" (PP.validate cfg.Cg.a (Dom.read s)) in
  let _   = Co.bprintflush mydebug "\nEND: PP.validate\n" in
  ({ sri          = sri
   ; ws           = ws
   ; negs         = cfg.Cg.negs
   (* stat *)
   ; tt           = Timer.create "fixpoint iters"
   ; stat_refines = ref 0
   ; stat_cfreqt  = Hashtbl.create 37
   }, s)
   >> (fun _ -> Co.bprintflush mydebug "DONE: Solve.create\n")


(* API *)
let create_deps cfg kf =
  let _ = Co.bprintflush mydebug "\nBEGIN: create_deps\n" in
  let group ls = 
    let rec go acc = function
      | [] -> acc
      | ((n,x)::xs) -> (
         if List.mem_assoc n acc
         then let ys = List.assoc n acc in 
              let _acc = List.remove_assoc n acc in 
               go ((n,(x::ys))::_acc) xs
         else go ((n,[x])::acc) xs
      ) in go [] ls in
  let cmp (n1,_) (n2,_) = compare n1 n2 in 
  let deps = cfg.Cg.deps |> group |> List.sort cmp in
  let rec addmore = function
    | [] -> []
    | ((n,xs)::xss) -> (n,xs) :: addmore (List.map begin fun (y,ys) ->
        (y,xs@ys) end xss) in 
  addmore deps
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: create_deps\n")

(* API *)
let create cfg kf (idi,ids) =
  let _ = Co.bprintflush mydebug "\nBEGIN: create\n" in
  let csi = 
    cfg.Cg.cs
    |> List.filter begin function c -> 
        List.mem (C.id_of_t c) ids
       end in
  let neg ss k = if List.mem k cfg.Cg.negs then ss k else None in 
  let wsi = List.filter begin function w -> 
        List.mem (C.id_of_wf w) ids
       end cfg.Cg.ws in 
  let (_csi,_wsi) = match kf with 
             | None -> (csi,wsi)
             | Some ss -> 
    (List.map (C.apply_partial_solution (neg ss)) csi,
     List.map (C.apply_partial_solution_wf (neg ss)) wsi) in 
  let cfgi = {cfg with Cg.cs = _csi; Cg.ws = _wsi} in
  let (x,y) =  create_one cfgi None in
  (idi, x, y)
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: create\n")
    
 
(* API *)
let save fname me s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" Ci.print me.sri;
  F.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" (C.print_wf None)) me.ws;
  F.fprintf ppf "@[%a@] \n" Dom.print s;
  close_out oc

(* API *)
let cone me = Cindex.data_cones (Ci.to_list me.sri)

end
