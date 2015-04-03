(* ========================================================================= *)
(* Prenex and Skolem normal forms.                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Get the functions in a term and formula.                                  *)
(* ------------------------------------------------------------------------- *)

fun funcs tm =
  case tm of
    Var x => []
  | Fn(f,args) => itlist (union_sip o funcs) args [(f,List.length args)];;
  
fun functions fm =
  atom_union_sip (fn (R(p,a)) => itlist (union_sip o funcs) a []) fm;;
  
(* TODO: All other functions *)
