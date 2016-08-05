(* ========================================================================= *)
(* Term orderings.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

fun termsize tm =
  case tm of
    Var x => 1
  | Fn(f,args) => itlist (fn t => fn n => termsize t + n) args 1;

(* ------------------------------------------------------------------------- *)
(* This fails the rewrite properties.                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;
val s = <<|"f(x,x,x)"|>>;
val t = <<|"g(x,y)"|>>;

termsize s > termsize t;

val i = ("y" |==> (<<|"f(x,x,x)"|>>));

termsize (tsubst i s) > termsize (tsubst i t);
END_INTERACTIVE;

(* TODO: All other functions *)
