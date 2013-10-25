(* 
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

type t


type 'a possoln = 
  (int * int) * 
   ((int*int)*
    (Ast.Symbol.t * 'a array)
    ) 
    array
  

  
type 'a mapsol = 'a  Ast.Symbol.SMap.t 

type 'a lattice = ('a array) Ast.Symbol.SMap.t 

type elem = Qualifier.t list

(*
val go_up : 'a array  -> ('a list * int list) list -> ('a list * int list) list

val make_lattice_one : 'a list  -> 'a list list
val  make_lattice : elem mapsol -> elem lattice


val _init_soln : 'a lattice -> 'a possoln

val init_soln : elem mapsol -> elem possoln
val soln_to_map : elem possoln -> elem mapsol
val next_element : elem possoln -> elem possoln option 

*)

module type SOLVER = sig
  type soln
  type bind
  val create    : bind FixConfig.cfg -> FixConstraint.psoln option -> (int * (int list))-> (int * t * soln)
  val create_deps : bind FixConfig.cfg -> FixConstraint.soln option -> (int * (int list) ) list
  val solve     : (int * t *soln) -> (soln * (FixConstraint.t list) *
  Counterexample.cex list) list 
  val save      : string -> t -> soln -> unit 
  val read      : soln -> FixConstraint.soln
  val min_read  : soln -> FixConstraint.soln
  val read_bind : soln -> Ast.Symbol.t -> bind
  val cone      : t -> FixConstraint.id -> FixConstraint.tag Ast.Cone.t
  (* val meet   : soln -> soln -> soln *)

end

module Make (Dom : SolverArch.DOMAIN) : SOLVER 
  with type bind = Dom.bind 
  with type soln = Dom.t
