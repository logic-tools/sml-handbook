(* ========================================================================= *)
(* Simple algebraic expression example from the introductory chapter.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* TODO: Expression *)

(* ------------------------------------------------------------------------- *)
(* Trivial example of using the type constructors.                           *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Simplification example.                                                   *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Lexical analysis.                                                         *)
(* ------------------------------------------------------------------------- *)

fun matches s = 
	let val chars = String.explode s in 
	fn c => mem c chars
	end;;

val space = matches " \t\n\r";;
val punctuation = matches "()[]{},";;
val symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/";;
val numeric = matches "0123456789";;
val alphanumeric = matches
  "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";;
  
fun lexwhile prop inp =
  if inp <> [] andalso prop (List.hd inp) then 
     let val (tok,rest) = lexwhile prop (List.tl inp) in 
	 ((str (List.hd inp))^tok,rest)
	 end
  else
     ("",inp);;
  
fun lex inp =
  case snd(lexwhile space inp) of
    [] => []
  | c::cs => let val prop = if alphanumeric(c) then alphanumeric
                        else if symbolic(c) then symbolic
                        else fn c => false 
                 val (toktl,rest) = lexwhile prop cs in
             ((str c)^toktl)::lex rest
			 end;;

START_INTERACTIVE;;
lex(String.explode "2*((var_1 + x') + 11)");;
lex(String.explode "if (*p1-- == *p2++) then f() else g()");;
END_INTERACTIVE;;
			 
(* ------------------------------------------------------------------------- *)
(* Parsing.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Generic function to impose lexing and exhaustion checking on a parser.    *)
(* ------------------------------------------------------------------------- *)

fun make_parser pfn s =
  let val (expr,rest) = pfn (lex(String.explode s)) in
  if rest = [] then expr else raise Fail "Unparsed input"
  end;;
  
(* ------------------------------------------------------------------------- *)
(* Our parser.                                                               *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Demonstrate automatic installation.                                       *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Conservatively bracketing first attempt at printer.                       *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Somewhat better attempt.                                                  *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Install it.                                                               *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Example shows the problem.                                                *)
(* ------------------------------------------------------------------------- *)

(* TODO *)
