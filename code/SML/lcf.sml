(* ========================================================================= *)
(* LCF-style basis for Tarski-style Hilbert system of first order logic.     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic first order deductive system.                                       *)
(*                                                                           *)
(* This is based on Tarski's trick for avoiding use of a substitution        *)
(* primitive. It seems about the simplest possible system we could use.      *)
(*                                                                           *)
(*  if |- p ==> q and |- p then |- q                                         *)
(*  if |- p then |- forall x. p                                              *)
(*                                                                           *)
(*  |- p ==> (q ==> p)                                                       *)
(*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
(*  |- ((p ==> false) ==> false) ==> p                                       *)
(*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
(*  |- p ==> forall x. p                            [x not free in p]        *)
(*  |- exists x. x = t                              [x not free in t]        *)
(*  |- t = t                                                                 *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
(*                                                                           *)
(*  |- (p <=> q) ==> p ==> q                                                 *)
(*  |- (p <=> q) ==> q ==> p                                                 *)
(*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
(*  |- true <=> (false ==> false)                                            *)
(*  |- ~p <=> (p ==> false)                                                  *)
(*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
(*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
(*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
(* ------------------------------------------------------------------------- *)

signature PROOFSYSTEM =
sig
    type thm
       val modusponens : thm -> thm -> thm
       val gen : string -> thm -> thm
       val axiom_addimp : fol formula -> fol formula -> thm
       val axiom_distribimp :
            fol formula -> fol formula -> fol formula -> thm
       val axiom_doubleneg : fol formula -> thm
       val axiom_allimp : string -> fol formula -> fol formula -> thm
       val axiom_impall : string -> fol formula -> thm
       val axiom_existseq : string -> term -> thm
       val axiom_eqrefl : term -> thm
       val axiom_funcong : string -> term list -> term list -> thm
       val axiom_predcong : string -> term list -> term list -> thm
       val axiom_iffimp1 : fol formula -> fol formula -> thm
       val axiom_iffimp2 : fol formula -> fol formula -> thm
       val axiom_impiff : fol formula -> fol formula -> thm
       val axiom_true : thm
       val axiom_not : fol formula -> thm
       val axiom_and : fol formula -> fol formula -> thm
       val axiom_or : fol formula -> fol formula -> thm
       val axiom_exists : string -> fol formula -> thm
       val concl : thm -> fol formula
end ;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions.                                                      *)
(* ------------------------------------------------------------------------- *)
  
fun occurs_in s t =
    s = t orelse
    case t of
      Var y => false
    | Fn(f,args) => List.exists (occurs_in s) args;;
    
fun free_in t fm =
    case fm of 
      False => false
    | True  => false
    | Atom(R(p,args)) => List.exists (occurs_in t) args
    | Not(p) => free_in t p
    | And(p,q) => (free_in t p) orelse (free_in t q)
    | Or(p,q)  => (free_in t p) orelse (free_in t q)
    | Imp(p,q) => (free_in t p) orelse (free_in t q)
    | Iff(p,q) => (free_in t p) orelse (free_in t q)
    | Forall(y,p) => not(occurs_in (Var y) t) andalso free_in t p
    | Exists(y,p) => not(occurs_in (Var y) t) andalso free_in t p;;

(* ------------------------------------------------------------------------- *)
(* Implementation of the abstract data type of theorems.                     *)
(* ------------------------------------------------------------------------- *)
    
structure Proven :> PROOFSYSTEM =
struct
    type thm = fol formula
    fun modusponens pq p =
        case pq of
          Imp(p',q) => 
            if p = p' then q 
            else raise Fail "modusponens"
        | _ =>   raise Fail "modusponens"
    fun gen x p = Forall(x,p)
    fun axiom_addimp p q = Imp(p,Imp(q,p))
    fun axiom_distribimp p q r =
      Imp(Imp(p,Imp(q,r)),Imp(Imp(p,q),Imp(p,r)))
    fun axiom_doubleneg p = Imp(Imp(Imp(p,False),False),p)
    fun axiom_allimp x p q =
      Imp(Forall(x,Imp(p,q)),Imp(Forall(x,p),Forall(x,q)))
    fun axiom_impall x p =
      if not (free_in (Var x) p) then Imp(p,Forall(x,p))
      else raise Fail "axiom_impall: variable free in formula"
    fun axiom_existseq x t =
      if not (occurs_in (Var x) t) then Exists(x,mk_eq (Var x) t)
      else raise Fail "axiom_existseq: variable free in term"
    fun axiom_eqrefl t = mk_eq t t
    fun axiom_funcong f lefts rights =
       itlist2 (fn s => fn t => fn p => Imp(mk_eq s t,p)) lefts rights
               (mk_eq (Fn(f,lefts)) (Fn(f,rights))) 
    fun axiom_predcong p lefts rights =
       itlist2 (fn s => fn t => fn p => Imp(mk_eq s t,p)) lefts rights
               (Imp(Atom(R(p,lefts)),Atom(R(p,rights))))
    fun axiom_iffimp1 p q = Imp(Iff(p,q),Imp(p,q))
    fun axiom_iffimp2 p q = Imp(Iff(p,q),Imp(q,p))
    fun axiom_impiff p q = Imp(Imp(p,q),Imp(Imp(q,p),Iff(p,q)))
    val axiom_true = Iff(True,Imp(False,False))
    fun axiom_not p = Iff(Not p,Imp(p,False))
    fun axiom_and p q = Iff(And(p,q),Imp(Imp(p,Imp(q,False)),False))
    fun axiom_or p q = Iff(Or(p,q),Not(And(Not(p),Not(q))))
    fun axiom_exists x p = Iff(Exists(x,p),Not(Forall(x,Not p)))
    fun concl c = c
  end;;
  
(* ------------------------------------------------------------------------- *)
(* A printer for theorems.                                                   *)
(* ------------------------------------------------------------------------- *)
  
open Proven;;

fun print_thm_aux th = (
    open_box 0;
    print_string "|-"; print_space();
    open_box 0; print_formula_aux print_atom_aux (concl th); close_box();
    close_box()
);;

fun print_thm th = (print_thm_aux th; print_flush ());;
