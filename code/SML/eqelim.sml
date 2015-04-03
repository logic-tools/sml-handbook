(* ========================================================================= *)
(* Equality elimination including Brand transformation and relatives.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen              *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Replacement (substitution for non-variable) in term and literal.          *)
(* ------------------------------------------------------------------------- *)

fun replacet rfn tm =
  apply_t rfn tm 
  handle Fail _ =>
  case tm of
    Fn(f,args) => Fn(f,List.map (replacet rfn) args)
  | _ => tm;;

(* TODO: All other functions *)
