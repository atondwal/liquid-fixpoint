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
  val create    : bind Cg.cfg -> FixConstraint.soln option -> (t * soln)
  val solve     : t -> soln -> (soln * (FixConstraint.t list) *
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

let make_lattice_one sm s qs = 
  let _  = Co.bprintflush mydebug "\nBEGIN: make_lattice_one \n" in
  let _  = F.printf "\n|QS| = %n \n" (List.length qs) ; flush stdout in

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
    make_lattice_one sm s <+> Array.of_list) ps
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

  let _ = F.printf "\n" in

  (Some ((ii,nn), aa)))
  | None -> None 

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

let unconstrained_kvars cs =
  let rhss = rhs_ks cs in
  cs  |> Misc.flap C.kvars_of_t
      |> List.map snd
      |> List.filter (fun kv -> not (Sy.SSet.mem kv rhss))

let true_unconstrained sri s =
  sri |> Ci.to_list 
      |> unconstrained_kvars
      |> Dom.top s

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











(* API *)
let solve me s = 
  let _  = Co.bprintflush mydebug "Fixpoint: Validating Initial Solution \n" in
  (* let _ = F.printf "create: SOLUTION \n %a \n" Dom.print s in *)
  let _  = BS.time "Prepass.profile" PP.profile me.sri in
  let _  = Co.bprintflush mydebug "\nBEGIN: Fixpoint: Trueing Unconstrained Variables \n" in
  let s  = s |> (!Co.true_unconstrained <?> BS.time "Prepass.true_unconstr" (true_unconstrained me.sri)) in
  let _  = Co.bprintflush mydebug "\nDONE: Fixpoint: Trueing Unconstrained Variables \n" in


  let (p0, sinit) = Dom.drop s me.negs in
  let p = p0 in
   

  let _  = Co.bprintflush mydebug "\nBEGIN: Exhaustive: Call init_soln \n" in
  let pm = init_soln me s p in

  let _  = Co.bprintflush mydebug "\nDONE: Exhaustive: Call init_soln \n" in
  let sups = loop s [] me pm sinit in

  (* update p *)
(* LOOP ENDS*)  
  let f s u = if !Co.cex && Misc.nonnull u then Dom.ctr_examples s (Ci.to_list me.sri) u else [] in
  let sup = List.map (fun (s, p) -> (Dom.add s p, [], [])) sups in 
  sup

let global_symbols cfg = 
     (SM.to_list cfg.Cg.uops)   (* specified globals *) 
  ++ (Theories.interp_syms)     (* theory globals    *)

(* API *)
let create cfg kf =
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



