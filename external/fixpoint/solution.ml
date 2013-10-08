(*
 * Copyright © 2009-11 The Regents of the University of California. 
 * All rights reserved. 
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
 *
 *)

(**
 * This module implements a module for representing and manipulating the intermediate solution of the variables.
 * *)
module Q = Qualifier

module F = Format

module Sy = Ast.Symbol
module SM = Sy.SMap
module SS = Sy.SSet

module Misc = FixMisc open Misc.Ops

let mydebug = true

(**************************************************************************)
(****************************** Bindings **********************************)
(**************************************************************************)

type 't b = Pos of 't list 
          | Neg of ('t list * 't list)

let init ?ispos:(p=true) x = if p then Pos x else Neg ([], x)

let def = Pos []

let get_bind = function Pos qs -> qs | Neg (qs, _) -> qs
let get_cand = function Pos qs -> qs | Neg (_, qs) -> qs

let set_bind x = function Pos _ -> Pos x | Neg (_,y) -> Neg(x,y)
let set_cand x = function Pos _ -> Pos x | Neg (y,_) -> Neg(y,x)

let map_bind f = function Pos x -> Pos (f x) | Neg (x, y) -> Neg (f x, y)

let is_pos = function Pos _ -> true | Neg _ -> false
let is_neg = function Neg _ -> true | Pos _ -> false

let meet_bind qs1 qs2 = 
    match (qs1, qs2) with
    | (Pos qs1, Pos qs2) ->  Pos (qs1 ++ qs2)
    | (Neg (qs1, cs1), Neg (qs2, cs2)) -> 
        (F.printf "meet_bind: S.Neg + Neg"; assert(false))
    | (_,_) -> (
        F.printf "meet_bind: Neg + S.Pos"; assert(false))


(* OLD SEETING *)

(*
type 't b = 't list 

let init ?ispos:(p=true) x = x

let def = []

let get_bind = id
let get_cand = id

let set_bind x _ = x
let set_cand x _ = x

let is_pos _ = true
let is_neg _ = false

let meet_bind qs1 qs2 = qs1 ++ qs2

*)


(******************************* Printing ************************************)


(*


let print_qmap = print_map


let print_full_qmap bm = 
 
  let print_qpair ppf (x, qs) = F.fprintf ppf "%s -> %a\n%a" (Sy.to_string x)
  (Misc.pprint_many true " , " Q.print) (S.get_bind qs) 
  (Misc.pprint_many true " , " Q.print) (S.get_cand qs) in 
  
  F.printf "Full Binding map = %a \n\n"
  (Misc.pprint_many true "\n" print_qpair) (SM.to_list bm)



*)
