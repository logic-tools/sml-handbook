(* ========================================================================= *)
(* Unification for first order terms.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

fun istriv env x t =
  case t of
    Var y => y = x orelse defined_str env y andalso istriv env x (apply_str env y)
  | Fn(f,args) => List.exists (istriv env x) args andalso raise Fail "cyclic";

(* ------------------------------------------------------------------------- *)
(* Main unification procedure                                                *)
(* ------------------------------------------------------------------------- *)

fun unify env eqs =
  case eqs of
    [] => env
  | (Fn(f,fargs),Fn(g,gargs))::oth =>
        if f = g andalso length fargs = length gargs
        then unify env (zip fargs gargs @ oth)
        else raise Fail "impossible unification"
  | (Var x,t)::oth =>
        if defined_str env x then unify env ((apply_str env x,t)::oth)
        else unify (if istriv env x t then env else (x|-->t) env) oth
  | (t,Var x)::oth =>
        if defined_str env x then unify env ((apply_str env x,t)::oth)
        else unify (if istriv env x t then env else (x|-->t) env) oth;

(* ------------------------------------------------------------------------- *)
(* Solve to obtain a single instantiation.                                   *)
(* ------------------------------------------------------------------------- *)

fun solve env =
  let val env' = mapf (tsubst env) env in
  if env' = env then env else solve env'
  end;

(* ------------------------------------------------------------------------- *)
(* Unification reaching a final solved form (often this isn't needed).       *)
(* ------------------------------------------------------------------------- *)

fun fullunify eqs = solve (unify undefined eqs);

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun unify_and_apply eqs =
  let val i = fullunify eqs
      fun apply (t1,t2) = (tsubst i t1,tsubst i t2) in
  map apply eqs
  end;

START_INTERACTIVE;
unify_and_apply [(<<|"f(x,g(y))"|>>,<<|"f(f(z),w)"|>>)];

unify_and_apply [(<<|"f(x,y)"|>>,<<|"f(y,x)"|>>)];

(****  unify_and_apply [(<<|"f(x,g(y))"|>>,<<|"f(y,x)"|>>)]; *****)

unify_and_apply [(<<|"x_0"|>>,<<|"f(x_1,x_1)"|>>),
                 (<<|"x_1"|>>,<<|"f(x_2,x_2)"|>>),
                 (<<|"x_2"|>>,<<|"f(x_3,x_3)"|>>)];
END_INTERACTIVE;
