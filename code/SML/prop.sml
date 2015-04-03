(* ========================================================================= *)
(* Basic stuff for propositional logic: datatype, parsing and printing.      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Disjunctive normal form (DNF) via truth tables.                           *)
(* ------------------------------------------------------------------------- *)

fun list_conj l = if l = [] then True else end_itlist mk_and l;;

(* TODO: All other functions *)
