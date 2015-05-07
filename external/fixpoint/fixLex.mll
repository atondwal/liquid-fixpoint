(*
 * Copyright � 1990-2002 The Regents of the University of California. All rights reserved. 
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
 * d 
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *)

{
  module Misc = FixMisc
  
  open Misc.Ops
  module E = Errorline
  open E
  open FixParse 

  let lexerror msg lexbuf = 
    E.error (Lexing.lexeme_start lexbuf) msg
 
  (* 
  let int_of_lexbuf lb = 
    let str = Lexing.lexeme lb in
    let len = String.length str in
    let zero = Char.code '0' in
    let rec accum a d =
      let acc c = a + (d * ((Char.code c) - zero)) in
      function 0 -> let c = str.[0] in
			  	    if c='-' then - a else (acc c)
		     | i -> accum (acc str.[i]) (d * 10) (i - 1)
    in accum 0 1 (len-1) 
   *)
  let safe_float_of_string s = 
    try float_of_string s with ex -> 
      let _ = Printf.printf "safe_float_of_string crashes on: %s (error = %s)" s (Printexc.to_string ex) in
      raise ex

  let safe_int_of_string s = 
    try int_of_string s with ex -> 
      let _ = Printf.printf "safe_int_of_string crashes on: %s (error = %s)" s (Printexc.to_string ex) in
      raise ex

  let string_suffix_from s n = String.sub s n (String.length s - n)

  let snip_begin_end str =
    let len = String.length str in
		String.sub str 1 (len-2)
                            
  (* let safe_big_int_of_string s = 
    try Big_int.big_int_of_string (string_suffix_from s 2) with ex -> 
      let _ = Printf.printf "safe_big_int_of_string crashes on: %s (error = %s)" s (Printexc.to_string ex) in
      raise ex
   *)


}

let digit    = ['0'-'9' '-']
let letdig   = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '@' ''' '.' '#']
let alphlet  = ['A'-'Z' 'a'-'z' '~' '_' ''' '@']
let capital  = ['A'-'Z']
let small    = ['a'-'z' '$' '_']
let ws       = [' ' '\009' '\012']
let pathname = ['a'-'z' 'A'-'Z' '0'-'9' '.' '/' '\\' '-']

rule token = parse
    ['\r''\t'' ']       { token lexbuf}
  | '\n'		        { begin
			                E.startNewline (Lexing.lexeme_end lexbuf);
			                token lexbuf 
			              end }
  | "//"[^'\n']*'\n'
                        { begin
                          E.startNewline (Lexing.lexeme_end lexbuf);
			              token lexbuf
                          end 
                        }
  | '_'                 { UNDERSCORE }
  | '['                 { LB }
  | ']'                 { RB }
  | '('			        { LPAREN }
  | ')'			        { RPAREN }
  | '{'			        { LC }
  | '}'			        { RC }
  | '~'                 { NOT }
  | ';'                 { SEMI }
  | ','                 { COMMA }
  | ':'                 { COLON }
  | '|'                 { MID }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { TIMES }
  | '/'                 { DIV }
  | '?'                 { QM }
  | '$'                 { DOL }
  | '.'                 { DOT }
  | "not"               { NOTWORD }
  | "tag"               { TAG }
  | "id"                { ID }
  | "Bexp"              { BEXP }
  | "false"             { FALSE }
  | "true"              { TRUE }
  | ":="                { ASGN }
  | "&&"                { AND }
  | "||"                { OR  }
  | "<=>"               { IFF }
  | "iff"               { IFFWORD }
  | "=>"                { IMPL }
  | "!="		        { NE }
  | "="		            { EQ }
  | "~~"		        { UEQ }
  | "!~"		        { UNE }
  | "<="		        { LE }
  | "<"		            { LT }
  | ">="		        { GE }
  | ">"		            { GT }
  | "mod"               { MOD }
  | "obj"               { OBJ }
  | "num"               { NUM }
  | "frac"              { FRAC }
  | "int"               { INT }
  | "real"              { REAL }
  | "ptr"               { PTR }
  | "<fun>"             { LFUN }
  (* | "fptr"           { FPTR } *)
  | "lit"               { LIT }
  | "bool"              { BOOL }
  | "uit"               { UNINT }
  | "func"              { FUNC }
  | "sort"              { SRT }
  | "axiom"             { AXM }
  | "constant"          { CON }
  | "constraint"        { CST }
  | "wf"                { WF }
  | "solution"          { SOL }
  | "qualif"            { QUL }
  | "cut"               { KUT }
  | "bind"              { BIND }
  | "add_dep"           { ADP }
  | "del_dep"           { DDP }
  | "env"               { ENV }
  | "grd"               { GRD }
  | "lhs"               { LHS }
  | "rhs"               { RHS }
  | "reft"              { REF }
  | "@"                 { TVAR } 
  | (digit)+'.'(digit)+	{ Real (safe_float_of_string (Lexing.lexeme lexbuf)) }
  | (digit)+	          { Num  (safe_int_of_string (Lexing.lexeme lexbuf)) }
  | (alphlet)letdig*	  { Id    (Lexing.lexeme lexbuf) }
  | '''[^''']*'''       { Id (snip_begin_end (Lexing.lexeme lexbuf)) }
  | '"'[^'"']*'"'       { StringLit (snip_begin_end (Lexing.lexeme lexbuf)) }
  | eof			            { EOF }
  | _			              { begin
                            lexerror ("Illegal Character '" ^ 
                                      (Lexing.lexeme lexbuf) ^ "'") lexbuf;
			                      token lexbuf
			                    end }

