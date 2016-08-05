(* ========================================================================= *)
(* Propositional reasoning by derived rules atop the LCF core.               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* |- p ==> p                                                                *)
(* ------------------------------------------------------------------------- *)

fun imp_refl p =
  modusponens (modusponens (axiom_distribimp p (Imp(p,p)) p)
                           (axiom_addimp p (Imp(p,p))))
              (axiom_addimp p p);

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> p ==> q                                          *)
(*               -------------------- imp_unduplicate                        *)
(*                 |- p ==> q                                                *)
(* ------------------------------------------------------------------------- *)

fun imp_unduplicate th =
  let val (p,pq) = dest_imp(concl th)
      val q = consequent pq in
  modusponens (modusponens (axiom_distribimp p p q) th) (imp_refl p)
  end ;

(* ------------------------------------------------------------------------- *)
(* Some handy syntax operations.                                             *)
(* ------------------------------------------------------------------------- *)

fun negatef fm =
  case fm of
    Imp(p,False) => p
  | p => Imp(p,False);

fun negativef fm =
  case fm of
    Imp(p,False) => true
  | _ => false;

(* ------------------------------------------------------------------------- *)
(*                           |- q                                            *)
(*         ------------------------------------------------ add_assum (p)    *)
(*                         |- p ==> q                                        *)
(* ------------------------------------------------------------------------- *)

fun add_assum p th = modusponens (axiom_addimp (concl th) p) th;

(* ------------------------------------------------------------------------- *)
(*                   |- q ==> r                                              *)
(*         --------------------------------------- imp_add_assum p           *)
(*           |- (p ==> q) ==> (p ==> r)                                      *)
(* ------------------------------------------------------------------------- *)

fun imp_add_assum p th =
  let val (q,r) = dest_imp(concl th) in
  modusponens (axiom_distribimp p q r) (add_assum p th)
  end;

(* ------------------------------------------------------------------------- *)
(*            |- p ==> q              |- q ==> r                             *)
(*         ----------------------------------------- imp_trans               *)
(*                 |- p ==> r                                                *)
(* ------------------------------------------------------------------------- *)

fun imp_trans th1 th2 =
  let val p = antecedent(concl th1) in
  modusponens (imp_add_assum p th2) th1
  end;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> r                                                *)
(*         -------------------------- imp_insert q                           *)
(*              |- p ==> q ==> r                                             *)
(* ------------------------------------------------------------------------- *)

fun imp_insert q th =
  let val (p,r) = dest_imp(concl th) in
  imp_trans th (axiom_addimp r q)
  end ;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> q ==> r                                          *)
(*              ---------------------- imp_swap                              *)
(*                 |- q ==> p ==> r                                          *)
(* ------------------------------------------------------------------------- *)

fun imp_swap th =
  let val (p,qr) = dest_imp(concl th)
      val (q,r) = dest_imp qr in
  imp_trans (axiom_addimp q p)
            (modusponens (axiom_distribimp p q r) th)
  end;

(* ------------------------------------------------------------------------- *)
(* |- (q ==> r) ==> (p ==> q) ==> (p ==> r)                                  *)
(* ------------------------------------------------------------------------- *)

fun imp_trans_th p q r =
   imp_trans (axiom_addimp (Imp(q,r)) p)
             (axiom_distribimp p q r);

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> q                                                *)
(*         ------------------------------- imp_add_concl r                   *)
(*          |- (q ==> r) ==> (p ==> r)                                       *)
(* ------------------------------------------------------------------------- *)

fun imp_add_concl r th =
  let val (p,q) = dest_imp(concl th) in
  modusponens (imp_swap(imp_trans_th p q r)) th
  end;

(* ------------------------------------------------------------------------- *)
(* |- (p ==> q ==> r) ==> (q ==> p ==> r)                                    *)
(* ------------------------------------------------------------------------- *)

fun imp_swap_th p q r =
  imp_trans (axiom_distribimp p q r)
            (imp_add_concl (Imp(p,r)) (axiom_addimp q p));

(* ------------------------------------------------------------------------- *)
(*  |- (p ==> q ==> r) ==> (s ==> t ==> u)                                   *)
(* -----------------------------------------                                 *)
(*  |- (q ==> p ==> r) ==> (t ==> s ==> u)                                   *)
(* ------------------------------------------------------------------------- *)

fun imp_swap2 th =
  case concl th of
    Imp(Imp(p,Imp(q,r)),Imp(s,Imp(t,u))) =>
        imp_trans (imp_swap_th q p r) (imp_trans th (imp_swap_th s t u))
  | _ => raise Fail "imp_swap2";

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r and |- p ==> q then |- p ==> r.                       *)
(* ------------------------------------------------------------------------- *)

fun right_mp ith th =
  imp_unduplicate(imp_trans th (imp_swap ith));

(* ------------------------------------------------------------------------- *)
(*                 |- p <=> q                                                *)
(*                ------------ iff_imp1                                      *)
(*                 |- p ==> q                                                *)
(* ------------------------------------------------------------------------- *)

fun iff_imp1 th =
  let val (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp1 p q) th
  end;

(* ------------------------------------------------------------------------- *)
(*                 |- p <=> q                                                *)
(*                ------------ iff_imp2                                      *)
(*                 |- q ==> p                                                *)
(* ------------------------------------------------------------------------- *)

fun iff_imp2 th =
  let val (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp2 p q) th
  end;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q      |- q ==> p                                        *)
(*        ---------------------------- imp_antisym                           *)
(*              |- p <=> q                                                   *)
(* ------------------------------------------------------------------------- *)

fun imp_antisym th1 th2 =
  let val (p,q) = dest_imp(concl th1) in
  modusponens (modusponens (axiom_impiff p q) th1) th2
  end;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> (q ==> false) ==> false                                  *)
(*       ----------------------------------- right_doubleneg                 *)
(*               |- p ==> q                                                  *)
(* ------------------------------------------------------------------------- *)

fun right_doubleneg th =
  case concl th of
    Imp(_,Imp(Imp(p,False),False)) => imp_trans th (axiom_doubleneg p)
  | _ => raise Fail "right_doubleneg";

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*         ------------------------------------------- ex_falso (p)          *)
(*                 |- false ==> p                                            *)
(* ------------------------------------------------------------------------- *)

fun ex_falso p = right_doubleneg(axiom_addimp False (Imp(p,False)));

(* ------------------------------------------------------------------------- *)
(*  |- p ==> q ==> r        |- r ==> s                                       *)
(* ------------------------------------ imp_trans2                           *)
(*      |- p ==> q ==> s                                                     *)
(* ------------------------------------------------------------------------- *)

fun imp_trans2 th1 th2 =
  let val Imp(p,Imp(q,r)) = concl th1
      val Imp(r',s) = concl th2
      val th = imp_add_assum p (modusponens (imp_trans_th q r s) th2) in
  modusponens th th1
  end;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q1   ...   |- p ==> qn   |- q1 ==> ... ==> qn ==> r      *)
(*        --------------------------------------------------------------     *)
(*                             |- p ==> r                                    *)
(* ------------------------------------------------------------------------- *)

fun imp_trans_chain ths th =
  itlist (fn a => fn b => imp_unduplicate (imp_trans a (imp_swap b))) (List.rev(List.tl ths)) (imp_trans (List.hd ths) th);

(* ------------------------------------------------------------------------- *)
(* |- (q ==> false) ==> p ==> (p ==> q) ==> false                            *)
(* ------------------------------------------------------------------------- *)

fun imp_truefalse p q =
  imp_trans (imp_trans_th p q False) (imp_swap_th (Imp(p,q)) p False);

(* ------------------------------------------------------------------------- *)
(*  |- (p' ==> p) ==> (q ==> q') ==> (p ==> q) ==> (p' ==> q')               *)
(* ------------------------------------------------------------------------- *)

fun imp_mono_th p p' q q' =
  let val th1 = imp_trans_th (Imp(p,q)) (Imp(p',q)) (Imp(p',q'))
      val th2 = imp_trans_th p' q q'
      val th3 = imp_swap(imp_trans_th p' p q) in
  imp_trans th3 (imp_swap(imp_trans th2 th1))
  end;

(* ------------------------------------------------------------------------- *)
(* |- true                                                                   *)
(* ------------------------------------------------------------------------- *)

val truth = modusponens (iff_imp2 axiom_true) (imp_refl False);

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q                                                        *)
(*      ----------------- contrapos                                          *)
(*         |- ~q ==> ~p                                                      *)
(* ------------------------------------------------------------------------- *)

fun contrapos th =
  let val (p,q) = dest_imp(concl th) in
  imp_trans (imp_trans (iff_imp1(axiom_not q)) (imp_add_concl False th))
            (iff_imp2(axiom_not p))
  end;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> p                                                           *)
(* ------------------------------------------------------------------------- *)

fun and_left p q =
  let val th1 = imp_add_assum p (axiom_addimp False q)
      val th2 = right_doubleneg(imp_add_concl False th1) in
  imp_trans (iff_imp1(axiom_and p q)) th2
  end;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> q                                                           *)
(* ------------------------------------------------------------------------- *)

fun and_right p q =
  let val th1 = axiom_addimp (Imp(q,False)) p
      val th2 = right_doubleneg(imp_add_concl False th1) in
  imp_trans (iff_imp1(axiom_and p q)) th2
  end;

(* ------------------------------------------------------------------------- *)
(* |- p1 /\ ... /\ pn ==> pi for each 1 <= i <= n (input term right assoc)   *)
(* ------------------------------------------------------------------------- *)

fun conjths fm =
  let val (p,q) = dest_and fm in
      (and_left p q)::List.map (imp_trans (and_right p q)) (conjths q)
  end handle Fail _ => [imp_refl fm];

(* ------------------------------------------------------------------------- *)
(* |- p ==> q ==> p /\ q                                                     *)
(* ------------------------------------------------------------------------- *)

fun and_pair p q =
  let val th1 = iff_imp2(axiom_and p q)
      val th2 = imp_swap_th (Imp(p,Imp(q,False))) q False
      val th3 = imp_add_assum p (imp_trans2 th2 th1) in
  modusponens th3 (imp_swap (imp_refl (Imp(p,Imp(q,False)))))
  end;

(* ------------------------------------------------------------------------- *)
(* If |- p /\ q ==> r then |- p ==> q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

fun shunt th =
  let val (p,q) = dest_and(antecedent(concl th)) in
  modusponens (itlist imp_add_assum [p,q] th) (and_pair p q)
  end;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r then |- p /\ q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

fun unshunt th =
  let val (p,qr) = dest_imp(concl th)
      val (q,r) = dest_imp qr in
  imp_trans_chain [and_left p q, and_right p q] th
  end;

(* ------------------------------------------------------------------------- *)
(* Produce |- (p <=> q) <=> (p ==> q) /\ (q ==> p)                           *)
(* ------------------------------------------------------------------------- *)


fun iff_def p q = (* Not in the book *)
  let val th1 = and_pair (Imp(p,q)) (Imp(q,p))
      val th2 = imp_trans_chain [axiom_iffimp1 p q, axiom_iffimp2 p q] th1 in
  imp_antisym th2 (unshunt (axiom_impiff p q))
  end;

fun iff_def p q =
  let val th = and_pair (Imp(p,q)) (Imp(q,p))
      val thl = [axiom_iffimp1 p q, axiom_iffimp2 p q] in
  imp_antisym (imp_trans_chain thl th) (unshunt (axiom_impiff p q))
  end;

(* ------------------------------------------------------------------------- *)
(* Produce "expansion" theorem for defined connectives.                      *)
(* ------------------------------------------------------------------------- *)

fun expand_connective fm =
  case fm of
    True => axiom_true
  | Not p => axiom_not p
  | And(p,q) => axiom_and p q
  | Or(p,q) => axiom_or p q
  | Iff(p,q) => iff_def p q
  | Exists(x,p) => axiom_exists x p
  | _ => raise Fail "expand_connective";

fun eliminate_connective fm =
  if not(negativef fm) then iff_imp1(expand_connective fm)
  else imp_add_concl False (iff_imp2(expand_connective(negatef fm)));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   ------------------------------------------------- imp_false_conseqs     *)
(*      [|- ((p ==> q) ==> false) ==> (q ==> false);                         *)
(*       |- ((p ==> q) ==> false) ==> p]                                     *)
(* ------------------------------------------------------------------------- *)

fun imp_false_conseqs p q =
 [right_doubleneg(imp_add_concl False (imp_add_assum p (ex_falso q))),
  imp_add_concl False (imp_insert p (imp_refl q))];

(* ------------------------------------------------------------------------- *)
(*         |- p ==> (q ==> false) ==> r                                      *)
(*        ------------------------------------ imp_false_rule                *)
(*             |- ((p ==> q) ==> false) ==> r                                *)
(* ------------------------------------------------------------------------- *)

fun imp_false_rule th =
  let val (p,r) = dest_imp (concl th) in
  imp_trans_chain (imp_false_conseqs p (funpow 2 antecedent r)) th
  end;

(* ------------------------------------------------------------------------- *)
(*         |- (p ==> false) ==> r          |- q ==> r                        *)
(*       ---------------------------------------------- imp_true_rule        *)
(*                      |- (p ==> q) ==> r                                   *)
(* ------------------------------------------------------------------------- *)

fun imp_true_rule th1 th2 =
  let val p = funpow 2 antecedent (concl th1)
      val q = antecedent(concl th2)
      val th3 = right_doubleneg(imp_add_concl False th1)
      val th4 = imp_add_concl False th2
      val th5 = imp_swap(imp_truefalse p q)
      val th6 = imp_add_concl False (imp_trans_chain [th3, th4] th5)
      val th7 = imp_swap(imp_refl(Imp(Imp(p,q),False))) in
  right_doubleneg(imp_trans th7 th6)
  end;

(* ------------------------------------------------------------------------- *)
(*                                 *                                         *)
(*                 -------------------------------------- imp_contr          *)
(*                        |- p ==> -p ==> q                                  *)
(* ------------------------------------------------------------------------- *)

fun imp_contr p q =
  if negativef p then imp_add_assum (negatef p) (ex_falso q)
  else imp_swap (imp_add_assum p (ex_falso q));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------------------- imp_front (this antecedent) *)
(*  |- (p0 ==> p1 ==> ... ==> pn ==> q)                                      *)
(*     ==> pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                              *)
(* ------------------------------------------------------------------------- *)

fun imp_front_th n fm =
  if n = 0 then imp_refl fm else
  let val (p,qr) = dest_imp fm
      val th1 = imp_add_assum p (imp_front_th (n - 1) qr)
      val (q',r') = dest_imp(funpow 2 consequent(concl th1)) in
  imp_trans th1 (imp_swap_th p q' r')
  end;

(* ------------------------------------------------------------------------- *)
(*           |- p0 ==> p1 ==> ... ==> pn ==> q                               *)
(*         ------------------------------------------ imp_front n            *)
(*           |- pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                         *)
(* ------------------------------------------------------------------------- *)

fun imp_front n th = modusponens (imp_front_th n (concl th)) th;

(* ------------------------------------------------------------------------- *)
(* Propositional tableaux procedure.                                         *)
(* ------------------------------------------------------------------------- *)

fun is_false False = true
  | is_false _ = false;

fun is_true (Imp(p,q)) = (p = q)
  | is_true _ = false;

fun is_conj (Imp(Imp(p,q),False)) = true
  | is_conj _ = false

fun dest_conj fm =
    case fm of
      (Imp(Imp(p,q),False)) => (p,q)
    | _ => raise Fail "dest_conj"

fun is_disj (Imp(p,q)) = (q <> False)
  | is_disj _ = false

fun dest_disj fm = dest_imp fm;

fun is_prop_lit p =
  case p of
     Atom(_) => true | Forall(_,_) => true | Imp(Atom(_),False) => true | Imp(Forall(_),False) => true
   | _ => false ;

fun lcfptab fms lits =
    case fms of
      []     => raise Fail "lcfptab: no contradiction"
    | fm::fl =>
        if is_false fm then (
            ex_falso (itlist mk_imp (fl @ lits) False)
        ) else if is_true fm then (
            add_assum fm (lcfptab fl lits)
        ) else if is_conj fm then (
            let val (p,q)=dest_conj fm in
            imp_false_rule(lcfptab (p::Imp(q,False)::fl) lits)
            end
        ) else if is_disj fm then (
            let val (p,q)=dest_disj fm in
            imp_true_rule (lcfptab (Imp(p,False)::fl) lits) (lcfptab (q::fl) lits)
            end
        ) else if is_prop_lit fm then (
            if mem (negatef fm) lits then
              let val (l1,l2) = chop_list (index (negatef fm) lits) lits
                  val th = imp_contr fm (itlist mk_imp (List.tl l2) False ) in
              itlist imp_insert (fl @ l1) th
              end
            else imp_front (List.length fl) (lcfptab fl (fm::lits))
        ) else ( (* is nonprimitive *)
           let val th = eliminate_connective fm in
           imp_trans th (lcfptab (consequent(concl th)::fl) lits)
           end
        )
;


(* ------------------------------------------------------------------------- *)
(* In particular, this gives a tautology prover.                             *)
(* ------------------------------------------------------------------------- *)

fun lcftaut p =
  modusponens (axiom_doubleneg p) (lcfptab [negatef p] []);

(* ------------------------------------------------------------------------- *)
(* The examples in the text.                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;
lcftaut (<<"(p ==> q) \\/ (q ==> p)">>);

lcftaut (<<"p /\\ q <=> ((p <=> q) <=> p \\/ q)">>);

lcftaut (<<"((p <=> q) <=> r) <=> (p <=> (q <=> r))">>);
END_INTERACTIVE;
