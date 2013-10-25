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
(* module TP   = TpNull.Prover *)
module Misc = FixMisc open Misc.Ops


let mydebug = true 
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
  val solve     : (int * t * soln)  -> (soln * (FixConstraint.t list) *
  Counterexample.cex list) list 
  val save      : string -> t -> soln -> unit 
  val read      : soln -> FixConstraint.soln
  val min_read  : soln -> FixConstraint.soln
  val read_bind : soln -> Ast.Symbol.t -> bind
  val cone      : t -> FixConstraint.id -> FixConstraint.tag Ast.Cone.t
  (* val meet   : soln -> soln -> soln  *)
end

type 'a possoln = 
  (int * int) * 
   ((int*int)*
    (Ast.Symbol.t * 'a array)
    ) 
    array
  

  
type 'a mapsol = 'a SM.t 
type 'a lattice = ('a  array) Ast.Symbol.SMap.t 

type elem = Qualifier.t list
(*
let go_up qs old =
  let _  = Co.bprintflush mydebug "\nBEGIN: go_up \n" in
  let _  = F.printf "\n|QS| = %n  - |OLD| = %n \n" nq nw ; flush stdout in
  let rec igo i acc =
    let _ = F.printf "\ni = %d \t\t |ACC| = %d\n" i (List.length acc); flush stdout in 
    if i >= nq 
    then acc 
    else let acc' = jgo i (i+1) [] in igo (i+1) (acc++acc')
  and jgo i j acc = 
    let _ = F.printf "\nj = %d \t\t |ACC| = %d\n" j  (List.length acc); flush stdout in 
    if j >= nw 
    then acc 
    else jgo i (j+1) (((Array.get qs i)::(Array.get ws j))::acc)
  in igo 0 []
  >> (fun xs -> F.printf "\n|NEXT| = %d \n" (List.length xs); flush stdout)
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: go_up \n")
*)


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
       Co.bprintf mydebug "ITERFREQ: %d times (ch = %b) %d constraints %s \n"
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
(******************** Iterative Refinement *********************)
(***************************************************************)

let rec remove i = function 
    | [] -> []
    | (x::xs) -> if x = i then xs else x :: remove i xs

let go_up qs old =
  let _  = Co.bprintflush mydebug "\nBEGIN: go_up \n" in
  let _  = F.printf "\n|QS| = %n  - |OLD| = %n \n" (Array.length qs) (List.length old) ; flush stdout in

  let f (x, is) = List.map (fun i -> 
    (Array.get qs i :: x, List.filter (fun x -> x != i) is)) is in 

  old |> List.map f |> List.concat
  
  >> (fun xs -> F.printf "\n|NEXT| = %d \n" (List.length xs); flush stdout)
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: go_up \n")


let is_min s ds = 
  let ds' = Dom.min_binds s ds in 
  List.length ds' == List.length ds

let make_lattice_one k sm s qs = 
  let _  = Co.bprintflush mydebug "\nBEGIN: make_lattice_one \n" in
  let _  = F.printf "\nfor %s|QS| = %n \n" (Sy.to_string k) (List.length qs) ; flush stdout in

  let (cqs, qs) = List.partition (fun q -> 
    (Q.pred_of_t <+> P.is_contra) q
    ) qs in

  let a = Array.of_list qs in
  let nq = List.length qs in
  let rec go n acc now = 
    match go_up a now with 
      | [] -> acc
      | [(qss,[])] -> acc @ [qss]
      | [_] -> (F.printf "make_lattice" ; assert (false); [])
      | qss   -> (
                  let _ = F.printf "\nStart is simple |qss| = %d\n" (List.length qss) in
                  
                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\nSIMPLE = %s \n%a\n" 
                  (if is_min s qs then "true"  else "false")
                  (Misc.pprint_many false " , " Q.print) qs
                  ) qss in
                  *)
                  
                  let qss = List.filter (fun (qs, _) -> is_min s qs) qss in
                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\n%a\n" (Misc.pprint_many false " , " Q.print) qs
                  ) qss in
                  *)
                  let _ = F.printf "\nEnd is simple |qss| = %d\n" (List.length qss) in


                  
                  let _ = F.printf "\nStart is contra |qss| = %d\n" (List.length qss) in

                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\nCONTRA = %s \n%a\n" 
                  (if Dom.is_contra sm s qs then "true"  else "false")
                  (Misc.pprint_many false " , " Q.print) qs
                  ) qss in

                  *)
                  let qss = List.filter (fun (qs, _) -> not (Dom.is_contra sm s qs)) qss in
                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\n%a\n" (Misc.pprint_many false " , " Q.print) qs
                  ) qss in
                  *)
                  let _ = F.printf "\nEnd is contra |qss| = %d\n" (List.length qss) in
                 
                  let is_implied qs = List.exists (fun ds -> Dom.is_equiv sm s qs ds) acc in 

                  
                  let _ = F.printf "\nStart is implied |qss| = %d\n" (List.length qss) in
                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\nIMPLIED = %s \n%a\n" 
                  (if is_implied qs then "true"  else "false")
                  (Misc.pprint_many false " , " Q.print) qs
                  ) qss in
                  *)
                  
                  let qss = List.filter (fun (qs, _) -> not (is_implied qs)) qss in
                  (*
                  let _ = List.map (fun (qs, _) -> 
                  F.printf "\n%a\n" (Misc.pprint_many false " , " Q.print) qs
                  ) qss in
                  *)
                  let _ = F.printf "\nEnd is implied |qss| = %d\n" (List.length qss) in
                 
                  
                  let (_acc, _) = List.split qss in 

                  let __acc = acc @ _acc in
                  go (n+1) __acc qss)
  in 
  let rec range i j = 
    if (j == i) then [j] 
    else if j < i then []
    else (i:: range (i+1) j) 
  in
  let ns = range 0 (nq-1) in
  let qss = List.map (fun x -> [x]) qs in
  let qns = Array.mapi (fun i x -> ([x], range (i+1) (nq-1))) a |> Array.to_list in

  go 1 ([]::((* (List.map (fun x -> [x]) cqs)@ *) qss)) qns
  >> (fun _ -> Co.bprintflush mydebug "\nDONE: make_lattice_one \n")
 

let make_lattice ws s ps = 
  let _  = Co.bprintflush mydebug "\nBEGIN: make_lattice \n" in
  SM.mapi (fun k ds -> 
    let ws = List.filter 
    (fun w -> List.mem k 
       (List.map snd (C.kvars_of_reft (C.reft_of_wf w)))
    ) 
    ws in
    let wf = match ws with 
             | [wf] -> wf
             | _ -> (assert false) [] in
    ds |>

(*    let _ = F.printf "WF for %s = \n%a\n PREDS = \n%a\n" 
                  (Sy.to_string k) 
                  (C.print_wf None) wf 
                  
                  (Misc.pprint_many false "\n" 
                  
                  
                  
                  (fun ppf (k, ps) -> F.fprintf ppf "%s :: %a" 
                  
                  (Sy.to_string k) 
                  (Misc.pprint_many false "\t&&\r" 
                    Ast.Predicate.print) ps
                  
                  )) 
                  (SM.to_list (SM.map 
                  (C.preds_of_reft (fun _ -> []))
                  (C.env_of_wf wf)))
    in 
*)
    let sm = SM.map (fun (_, x, _) -> x) (C.env_of_wf wf) in 
    make_lattice_one k sm s <+> Array.of_list) ps
(*
    >> (fun m -> SM.mapi (fun k -> (Array.mapi (fun i qs -> F.printf "\nLSIZE for %s at %d = %d" 
  (Sy.to_string k) i (List.length qs)))) m)
    >> (fun _ -> Co.bprintflush mydebug "\nDONE: make_lattice \n")
*)

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

  if n > 0 then (
  let _ = F.printf "\nBEGIN: next_element\n" in 
  let rec go ii aa = 
    let _ = F.printf "\nBEGIN: go (ii = %d)\n" ii in
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

  let _ = F.printf "\nEND: next_element\n" in

  (Some ((ii,nn), aa)))
  | None -> (F.printf "\nEND: next_element\n" ; None) 
  ) else None 
let is_solved s c = 
  let sol = read s in
  c |> C.rhs_of_t 
    |> C.kvars_of_reft
    |> List.map (sol <.> snd)
    |> List.for_all ((=) [])

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
(* 
let true_unconstrained sri s = 
  if !Co.true_unconstrained then 
    let _ = Co.logPrintf "Fixpoint: Pruning unconstrained kvars \n" 
    in true_unconstrained sri s
  else 
    let _ = Co.logPrintf "Fixpoint: NOT Pruning unconstrained kvars \n" 
    in s
*)
let print_s s = 
F.printf "SOLUTION = %a" Dom.print s 


let print_p p 
 = 
   F.printf "\nBEGIN P"; 
   SM.mapi begin  
     fun k ds -> F.printf "\n(S = %d) %s = %a" 
     (List.length ds) (Sy.to_string k)
     (Misc.pprint_many false ", " Q.print_pred) ds
   end p;
   F.printf "\nEND P\n" 



let rec loop s acc me pm sinit =

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



(*
    
    let wf = match ws with 
             | [wf] -> wf
             | _ -> (assert false) [] in
    ds |>

    let _ = F.printf "WF for %s = \n%a\n PREDS = \n%a\n" 
                  (Sy.to_string k) 
                  (C.print_wf None) wf 
                  
                  (Misc.pprint_many false "\n" 
                  
                  
                  
                  (fun ppf (k, ps) -> F.fprintf ppf "%s :: %a" 
                  
                  (Sy.to_string k) 
                  (Misc.pprint_many false "\t&&\r" 
                    Ast.Predicate.print) ps
                  
                  )) 
                  (SM.to_list (SM.map 
                  (C.preds_of_reft (fun _ -> []))
                  (C.env_of_wf wf)))
    in 

*)





    if List.exists is_contra_wf negws || 
       List.exists (fun s -> List.for_all (is_implied_wf p (snd s)) negws) acc  then 
    match next_element pm with
                | None -> acc
                | Some pm' -> loop s acc me pm' sinit

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
                | Some pm' -> loop s acc me pm' sinit

      )









let nq = ref 0 

(* API *)
let solve_one me s = 
  let _  = Co.bprintflush mydebug "Fixpoint: Validating Initial Solution \n" in
  (* let _ = F.printf "create: SOLUTION \n %a \n" Dom.print s in *)
  let _  = BS.time "Prepass.profile" PP.profile me.sri in
  let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Trueing Unconstrained Variables \n" in
  let s  = s |> (!Co.true_unconstrained <?> BS.time "Prepass.true_unconstr" (true_unconstrained me.sri)) in
  let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Trueing Unconstrained Variables \n" in

(*   (*BEGIN: PRINTING DEPENDENCIES*)
  let kvars cs = Sy.SSet.union (envs_ks [cs]) (lhs_ks [cs]) 
             |> Sy.SSet.filter (fun k -> List.mem k (me.negs) ) in  

  let akvars cs = Sy.SSet.union (envs_ks [cs]) (lhs_ks [cs]) 
             |> Sy.SSet.union (rhs_ks [cs]) 
             |> Sy.SSet.filter (fun k -> List.mem k (me.negs) ) in  

  let pkvars cs = (lhs_ks [cs]) 
             |> Sy.SSet.filter (fun k -> not (List.mem k (me.negs) )) in  

  let prkvars cs = (rhs_ks [cs]) 
             |> Sy.SSet.filter (fun k -> not (List.mem k (me.negs) )) in  

  let pakvars cs = Sy.SSet.union (envs_ks [cs]) (lhs_ks [cs]) 
             |> Sy.SSet.union (rhs_ks [cs]) 
             |> Sy.SSet.filter (fun k -> not (List.mem k (me.negs) )) in  
 
  
  
  let bar cs = 
    let tid = C.id_of_t cs in 
    let kvs = kvars cs in 
    F.printf "\nid = %d := {%s}  {%s} {%s} {%s}" tid 
    (String.concat ", " (List.map Sy.to_string (Sy.SSet.elements kvs))) 
    (String.concat ", " (List.map Sy.to_string (Sy.SSet.elements (akvars cs)))) 
    (String.concat ", " (List.map Sy.to_string (Sy.SSet.elements (pkvars cs))))
    (String.concat ", " (List.map Sy.to_string (Sy.SSet.elements (pakvars cs)))); 
    (tid, kvs, akvars cs, pkvars cs, pakvars cs, prkvars cs) in 
  let foo = List.map bar (Ci.to_list me.sri) in 


  let all_kvars = List.fold_left begin function acc -> function (_,_,n,_,p,_) -> 
    Sy.SSet.union acc (Sy.SSet.union n p)
  end Sy.SSet.empty foo in 

  let _ = F.printf "\nALL KVARS = \n%s\n" 
  (String.concat "\t" (List.map Sy.to_string (Sy.SSet.elements all_kvars)))
  in  

  let deps = List.map begin function k -> 
    let incs = foo
             |> List.filter (function (_,ks1,_,_,_,ks2) -> 
                 Sy.SSet.mem k ks1 || Sy.SSet.mem k ks2)
             |> List.map (function (id,_,_,_,_,_) -> id) in 

        let outcs = foo
             |> List.filter (function (_,_,ks1,ks2,_,_) -> 
                 Sy.SSet.mem k ks1 || Sy.SSet.mem k ks2)
             |> List.map (function (id,_,_,_,_,_) -> id) in 

    
    
    (k,incs,outcs)
  end (Sy.SSet.elements all_kvars) in 

  let _ = F.printf "\nDEPENDENCIES\n\n" in 
  let _ = List.map begin function (k, incs, outcs) -> 
   F.printf "%s IN={%s} OUT={%s}\n"
   (Sy.to_string k)
   (String.concat ", " (List.map string_of_int incs))
   (String.concat ", " (List.map string_of_int outcs))
  end deps in 


  let _ = assert false in 

(*END PRINTING DEPENDENCIES*)
*)
  
  
  let (p0, sinit) = Dom.drop s me.negs in

 
  let puks = neg_true_unconstrained me.sri in
  let p0 = SM.filter (fun k _ -> not (Sy.SSet.mem k puks) ) p0 in
  let sinit = Dom.add sinit (SM.of_list (List.map (fun x -> (x, []))
  (Sy.SSet.elements puks)) ) in 
  
  let pempty = SM.map (fun _ -> [] ) p0 in 
  
  let sue k = if SM.mem k pempty
               then Some [Ast.pTrue] 
               else None in
  let mee    = {me with sri = Ci.wapply_psoln sue me.sri} in

    let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Initialize Worklist \n" in
    let we  = BS.time "Cindex.winit" Ci.winit mee.sri in 
    let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Initialize Worklist \n" in
 
    let _  = Co.bprintflush vmydebug "\nBEGIN: Fixpoint Refinement Loop \n" in
    let sie  = BS.time "Solve.acsolve"  (acsolve mee we) sinit in
    let _  = Co.bprintflush vmydebug "\nDONE: Fixpoint Refinement Loop \n" in
  (* let _ = F.printf "create: SOLUTION2 \n %a \n" Dom.print s in *)
    let _  = Co.bprintflush vmydebug "\nBEGIN: Simplify Solution \n" in
    let se  = if !Co.minquals then simplify_solution mee sie else sie in
    let _  = Co.bprintflush vmydebug "\nDONE: Simplify Solution \n" in
    let _  = if vmydebug then BS.time "Solve.dump" (dump mee) s else ()  in
    let _  = Co.bprintflush mydebug "Fixpoint: Testing Solution \n" in
    let ue  = BS.time "Solve.unsatcs" (unsat_constraints mee) sie in

 
    if (ue == []) then 
      (
        [(Dom.add se pempty, [], []) ]
    
    ) else
 ( 

  
  let p = p0 in
   

  let _  = Co.bprintflush mydebug "\nBEGIN: Exhaustive: Call init_soln \n" in
  let pm = init_soln me s p in

  let _  = Co.bprintflush mydebug "\nDONE: Exhaustive: Call init_soln \n" in

  let sups = loop s [] me pm sinit in

  (* update p *)
(* LOOP ENDS*)  
  let f s u = if !Co.cex && Misc.nonnull u then Dom.ctr_examples s (Ci.to_list me.sri) u else [] in
  let sup = List.map (fun (s, p) -> (Dom.add s p, [], [])) sups in 
  

  let create_q template pred = 
    let qname = incr nq; Sy.of_string 
    (String.concat "" ["DummyQ";(string_of_int !nq)]) in
    let qvar  = Q.vv_of_t template in 
    let qsort = Q.sort_of_t template in 
    Q.create qname qvar qsort [] pred in 


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
  in

  let union_one dss =  
     match List.concat (List.map fst dss) with 
      | [] -> []
      | (d::_) -> (
        let f (ds,epds) =
        let pds = List.map Q.pred_of_t ds in pds@epds
(*
        let pds = List.map Q.pred_of_t ds in
         let env  = C.env_of_wf w in
         let epds = SM.mapi begin fun i (v,s,rs) -> 
            let pds = C.preds_of_reft (fun _ -> []) (v,s,rs) in 
             List.map begin fun p -> 
               Ast.Predicate.subst p v (Ast.eVar i) end  pds
         end env
         in epds |> SM.bindings |> List.map snd |> List.concat
                 |> fun eps -> eps@pds
*)          
      in           
        let pd =  dss |> List.map (f <+> Ast.pAnd)
              |> Ast.pOr in  
        let qq = create_q d pd 
        in [qq]
      ) in

  let mapSnd f (x, y) = (x, f y) in 
 
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
      (ds, epds) end p in
                      

  let punion = 
     sups |> List.map snd
          |> List.map g
          |> List.map SM.bindings
          |> group 
          |> List.map (mapSnd union_one) 
         |> SM.of_list
  in
  
  let _ = SM.mapi begin
    fun k ds -> F.printf "%s := %a"
    (Sy.to_string k)
    (Misc.pprint_many false "\n" Q.print) ds
  end punion
    
    in




(*BEGIN : SOLVE WITH UNION *)

    let p = punion in 
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




  let sup = List.map (fun (s, p) -> (Dom.add s p, [], [])) sups in 





(* END : SOLVE WITH UNION *)
  let union_solution = [(Dom.add s p, u, []) ] in
  let one_solution = true in
  if one_solution then union_solution else sup

)


(*
let solve me s =
  let sinit = s in 
  let is_neg k = List.mem k me.negs in 
  let cs = Ci.to_list me.sri in
  let iks = List.map begin fun c -> 
    (C.id_of_t c, envs_ks [c] |> Sy.SSet.filter is_neg)
    end cs in

  
  let rec foo me s iks (pari, parns, accs) = 
  let sii = s in
  let meii = me in 
  match iks with 
  | [] -> [(accs,[],[])]
  | ((i,n)::css) -> begin
    let rec take (iis, nns) = function 
      |[] -> ((iis, nns), [])
      |((ii,nn)::_cs) -> (
          if ((Sy.SSet.is_empty nn && Sy.SSet.is_empty n)
            || (Sy.SSet.exists (fun i -> Sy.SSet.mem i nn) n)
          ) then take (ii::iis, Sy.SSet.union nn nns) _cs
            else ((iis, nns), _cs)) in
    let ((iis, nns), rest) = take ([], Sy.SSet.empty) css in 
    let nns = Sy.SSet.union n nns in 
    let iis = i::iis in 
    let sri = Ci.keep (iis@pari) me.sri in

    
    let (np,_) = Dom.drop accs parns  in
    let su k = if List.mem k parns
               then SM.find k np |>: Q.pred_of_t |> fun x -> Some x
               else None in
    let _me    = {me with sri = Ci.wapply_psoln su sri; negs=Sy.SSet.elements nns} in




    let [(sol,x,y)] = partial_solve _me s in 
    let _ = F.printf "%a" Dom.print sol in 
    let nsi = parns@(Sy.SSet.elements nns) in
    let (newp,_) = Dom.drop sol (nsi) in
    foo meii sii rest (iis@pari,nsi, Dom.add accs newp)
  end

  in 
  let [(sol,_,_)] = foo me s iks ([], [],s) in 

  let p = sol in 

  (*List.fold_left begin function sol -> function ([(p,_,_)],ns) -> 
    let (np,_) = Dom.drop p (Sy.SSet.elements ns) in
    Dom.add sol np
    end sol ps in 
  *)
  (* VALIDATE *)
  
    let (np,_) = Dom.drop p (me.negs) in
    let su k = if List.mem k (me.negs)
               then SM.find k np |>: Q.pred_of_t |> fun x -> Some x
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
    [(Dom.add s np,u,[])]
*)

let solve (i,me,s) = 
       let _ = F.printf "\nBEGIN: SOLVING %d\n" i in 
       let sol = solve_one me s in
       let _ = F.printf "\nEND : SOLVING %d\n" i in 
       sol

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
  let _ = F.printf "\nBEGIN: DEPS\n" in
  let deps = cfg.Cg.deps |> group |> List.sort cmp in
  let _ = List.map begin function (i,ns) -> 
     let _ = F.printf "\n\n%d:\t" i in 
     List.map begin function i -> F.printf "\t%d" i end ns
    end deps in

  let rec addmore = function
    | [] -> []
    | ((n,xs)::xss) -> (n,xs) :: addmore (List.map (fun (y,ys) ->(y,xs@ys) )
    xss) in
  let _ = F.printf "\nEND: DEPS\n" in addmore deps








let create cfg kf (idi,ids)=
  let _ = F.printf "\nBEGIN: CREATE FOR %d\n" idi in 
(*  let group ls = 
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
  let _ = F.printf "\nBEGIN: DEPS\n" in
  let deps = cfg.Cg.deps |> group |> List.sort cmp in
  let _ = List.map begin function (i,ns) -> 
     let _ = F.printf "\n\n%d:\t" i in 
     List.map begin function i -> F.printf "\t%d" i end ns
    end deps in 
  let _ = F.printf "\nEND: DEPS\n" in

  let rec loop acc deps = 
    match deps with 
    | [] -> acc
    | ((idi,ids) :: ndeps) ->*) (
  let csi = 
    cfg.Cg.cs
    |> List.filter begin function c -> 
        List.mem (C.id_of_t c) ids
       end in

  let wsi = List.filter begin function w -> 
        List.mem (C.id_of_wf w) ids
       end cfg.Cg.ws in 

  
  
  let neg ss k = if List.mem k cfg.Cg.negs then ss k else None in  
  
  let (_csi,_wsi) = match kf with 
             | None -> (csi,wsi)
             | Some ss -> 
  (List.map (C.apply_partial_solution (neg ss)) csi,
  List.map (C.apply_partial_solution_wf (neg ss)) wsi) in 

(*
  let _ = List.map begin function c -> 
   F.printf "\n%a\n" (C.print_t None) c
  end _csi in
*)
  let cfgi = {cfg with Cg.cs = _csi; Cg.ws = _wsi} in
  let (x,y) =  create_one cfgi None in
  let _ = F.printf "END: CREATE FOR %d" idi in 
  (idi, x, y)
    )
 
  (*in List.rev (loop [] deps) *)


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



