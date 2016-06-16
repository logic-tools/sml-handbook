(* ========================================================================= *)
(* Initialize theorem proving example code.                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

datatype dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;
use "initialization.sml";;
use "lib.sml";;
use "intro.sml";;
use "formulas.sml";;
use "prop.sml";;
use "fol.sml";;
use "skolem.sml";;
use "unif.sml";;
use "tableaux.sml";;
use "resolution.sml";;
use "equal.sml";;
use "order.sml";;
use "eqelim.sml";;
use "Proven-lcf.sml";;

open Proven;;

fun print_thm_aux th = (
    open_box 0;
    print_string "|-"; print_space();
    open_box 0; print_formula_aux print_atom_aux (concl th); close_box();
    close_box()
);;

fun print_thm th = (print_thm_aux th; print_flush ());;

use "lcfprop.sml";;
use "folderived.sml";;
use "lcffol.sml";;

type thm = fol_thm;;

use "tactics.sml";;
