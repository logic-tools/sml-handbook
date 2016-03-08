(* ========================================================================= *)
(* Resolution.                                                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Matching of terms and literals.                                           *)
(* ------------------------------------------------------------------------- *)

fun term_match env eqs =
    case eqs of
      [] => env
    | (Fn (f, fa), Fn(g, ga)) :: oth =>
        if (f = g andalso List.length fa = List.length ga) then
        term_match env (zip fa ga @ oth)
        else raise Fail  "term_match"
    | (Var x, t) :: oth =>
        if not (defined_str env x) then
            term_match ((x |--> t) env) oth
        else if apply_str env x = t then
            term_match env oth
        else
            raise Fail "term_match"
    | _ =>
        raise Fail "term_match";;
        
(* TODO: All other functions *)
