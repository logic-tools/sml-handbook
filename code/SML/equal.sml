(* ========================================================================= *)
(* First order logic with equality.                                          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

fun mk_eq s t = Atom(R("=",[s,t]));

fun dest_eq fm =
  case fm of
    Atom(R("=",[s,t])) => (s,t)
  | _ => raise Fail "dest_eq: not an equation";

fun lhs eq = fst (dest_eq eq) and rhs eq = snd (dest_eq eq);

(* TODO: All other functions *)
