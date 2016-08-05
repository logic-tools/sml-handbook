(* ========================================================================= *)
(* Tableaux, seen as an optimized version of a Prawitz-like procedure.       *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

fun deepen f n =
  (print_string "Searching with depth limit ";
      print_int n; print_newline(); f n
  )
  handle Fail _ => deepen f (n + 1);


(* TODO: All other functions *)
