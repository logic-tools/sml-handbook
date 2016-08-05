(* ========================================================================= *)
(* First order tableau procedure using LCF setup.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unification of complementary literals.                                    *)
(* ------------------------------------------------------------------------- *)

fun unify_complementsf env =
  fn (Atom(R(p1,a1)),Imp(Atom(R(p2,a2)),False)) => unify env [(Fn(p1,a1),Fn(p2,a2))]
   | (Imp(Atom(R(p1,a1)),False),Atom(R(p2,a2))) => unify env [(Fn(p1,a1),Fn(p2,a2))]
   | _ => raise Fail "unify_complementsf";


(* ------------------------------------------------------------------------- *)
(*    |- (q ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* --------------------------------------------- use_laterimp <<q ==> p>>    *)
(*    |- (p ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* ------------------------------------------------------------------------- *)

fun use_laterimp i fm =
  case fm of
    Imp(_,Imp(i',_)) =>
      ( case (fm,i'=i) of
          (Imp(Imp(q',s),Imp(i' as Imp(q,p),r)),true) =>
             let val th1 = axiom_distribimp i (Imp(Imp(q,s),r)) (Imp(Imp(p,s),r))
                 val th2 = imp_swap(imp_trans_th q p s)
                 val th3 = imp_swap(imp_trans_th (Imp(p,s)) (Imp(q,s)) r) in
             imp_swap2(modusponens th1 (imp_trans th2 th3))
             end
        | (Imp(qs,Imp(a,b)),_) =>
             imp_swap2(imp_add_assum a (use_laterimp i (Imp(qs,b))))
      )
;

(* ------------------------------------------------------------------------- *)
(* The "closure" inference rules.                                            *)
(* ------------------------------------------------------------------------- *)

fun imp_false_rule' th es = imp_false_rule(th es);

fun imp_true_rule' th1 th2 es = imp_true_rule (th1 es) (th2 es);

fun imp_front' n thp es = imp_front n (thp es);

fun add_assum' fm thp (es as(e,s)) =
  add_assum (onformula e fm) (thp es);

fun eliminate_connective' fm thp (es as(e,s)) =
  imp_trans (eliminate_connective (onformula e fm)) (thp es);

fun spec' y fm n thp (e,s) =
  let val th = imp_swap(imp_front n (thp(e,s))) in
  imp_unduplicate(imp_trans (ispec (e y) (onformula e fm)) th)
  end;

fun ex_falso' fms (e,s) =
  ex_falso (itlist (mk_imp o onformula e) fms s);

fun complits' (p::fl,lits) i (e,s) =
  let val (l1,p'::l2) = chop_list i lits in
  itlist (imp_insert o onformula e) (fl @ l1)
         (imp_contr (onformula e p)
                    (itlist (mk_imp o onformula e) l2 s))
  end;

fun deskol' (skh:fol formula) thp (e,s) =
  let val th = thp (e,s) in
  modusponens (use_laterimp (onformula e skh) (concl th)) th
  end;

(* ------------------------------------------------------------------------- *)
(* Main refutation function.                                                 *)
(* ------------------------------------------------------------------------- *)

fun is_lit (Atom(_)) = true
  | is_lit (Imp(Atom(_),False)) = true
  | is_lit _ = false;

fun is_uni (Forall(_,_)) = true
  | is_uni _ = false;

fun dest_uni (Forall(x,p)) = (x,p);

fun is_exi (Imp(Forall(_,_),False)) = true
  | is_exi _ = false;

fun dest_exi (Imp(yp as Forall(y,p),False)) = (y,p,yp);

fun lcftab skofun (fms,lits,n) cont (esk as (env,sks,k)) =
    if n < 0 then raise Fail "lcftab: no proof" else
    case fms of
      []     => raise Fail "lcftab: No contradiction"
    | fm::fl =>
        if is_false fm then (
            cont (ex_falso' (fl @ lits)) esk
        ) else if is_true fm then (
            lcftab skofun (fl,lits,n) (cont o add_assum' fm) esk
        ) else if is_conj fm then (
            let val (p,q)=dest_conj fm in
            lcftab skofun (p::Imp(q,False)::fl,lits,n) (cont o imp_false_rule') esk
            end
        ) else if is_disj fm then (
            let val (p,q)=dest_disj fm in
            lcftab skofun (Imp(p,False)::fl,lits,n) (fn th => lcftab skofun (q::fl,lits,n) (cont o imp_true_rule' th)) esk
            end
        ) else if is_lit fm then (
            (tryfind (fn p' => (
                let val env' = unify_complementsf env (fm, p') in
                cont (complits' (fms, lits) (index p' lits)) (env', sks, k)
                end)) lits)
            handle Fail _ => (
                lcftab skofun (fl,fm::lits,n) (cont o imp_front' (List.length fl)) esk
            )
        ) else if is_uni fm then (
            let val (x,p) = dest_uni fm
                val y = Var("X_"^(Int.toString k)) in
            lcftab skofun ((subst (x |==> y) p)::fl@[fm],lits,n-1)
                    (cont o spec' y fm (List.length fms)) (env,sks,k+1)
            end
        ) else if is_exi fm then (
            let val (y,p,yp) = dest_exi fm
                val fx = skofun yp
                val p' = subst(y |==> fx) p
                val skh = Imp(p',Forall(y,p))
                val sks' = (Forall(y,p),fx)::sks in
            lcftab skofun (Imp(p',False)::fl,lits,n) (cont o deskol' skh) (env,sks',k)
            end
        ) else ( (* is nonprimitive *)
           let val fm' = consequent(concl(eliminate_connective fm)) in
           lcftab skofun (fm'::fl,lits,n) (cont o eliminate_connective' fm) esk
           end
        )
;

(* ------------------------------------------------------------------------- *)
(* Identify quantified subformulas; true = exists, false = forall. This is   *)
(* taking into account the effective parity.                                 *)
(* NB: maybe I can use this in sigma/delta/pi determination.                 *)
(* ------------------------------------------------------------------------- *)

fun quantforms e fm =
  case fm of
    Not(p) => quantforms (not e) p
  | And(p,q) => union_folfm (quantforms e p) (quantforms e q)
  | Or(p,q)  => union_folfm (quantforms e p) (quantforms e q)
  | Imp(p,q) => quantforms e (Or(Not p,q))
  | Iff(p,q) => quantforms e (Or(And(p,q),And(Not p,Not q)))
  | Exists(x,p) => if e then fm::(quantforms e p) else quantforms e p
  | Forall(x,p) => if e then quantforms e p else fm::(quantforms e p)
  | _ => [];


(* ------------------------------------------------------------------------- *)
(* Now create some Skolem functions.                                         *)
(* ------------------------------------------------------------------------- *)

fun skolemfuns fm =
  let val fns = List.map (fn pr => fst pr) (functions fm)
      val skts = List.map (fn Exists(x,p) => Forall(x,Not p) | p => p)
                 (quantforms true fm)
      fun skofun i (ap as Forall(y,p)) =
            let val vars = List.map (fn v => Var v) (fv ap) in
            (ap,Fn(variant("f"^"_"^Int.toString i) fns,vars))
            end
  in
  map2 skofun (1--length skts) skts
  end;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun form_match (fp as (f1,f2)) env =
  case fp of
    (False,False) => env
  | (True,True)   => env
  | (Atom(R(p,pa)),Atom(R(q,qa))) => term_match env [(Fn(p,pa),Fn(q,qa))]
  | (Not(p1),Not(p2)) => form_match (p1,p2) env
  | (And(p1,q1),And(p2,q2)) => form_match (p1,p2) (form_match (q1,q2) env)
  | (Or(p1,q1),Or(p2,q2))   => form_match (p1,p2) (form_match (q1,q2) env)
  | (Imp(p1,q1),Imp(p2,q2)) => form_match (p1,p2) (form_match (q1,q2) env)
  | (Iff(p1,q1),Iff(p2,q2)) => form_match (p1,p2) (form_match (q1,q2) env)
  | (Forall(x1,p1),Forall(x2,p2)) =>
        if (x1=x2) then
          let val z = variant x1 (union_str (fv p1) (fv p2))
              val inst_fn = subst (x1 |==> Var z) in
          undefine_str z (form_match (inst_fn p1,inst_fn p2) env)
          end
        else
          raise Fail "form_match"
  | (Exists(x1,p1),Exists(x2,p2)) =>
        if (x1=x2) then
          let val z = variant x1 (union_str (fv p1) (fv p2))
              val inst_fn = subst (x1 |==> Var z) in
          undefine_str z (form_match (inst_fn p1,inst_fn p2) env)
          end
        else
          raise Fail "form_match"
  | _ => raise Fail "form_match";

(* ------------------------------------------------------------------------- *)
(* With the current approach to picking Skolem functions.                    *)
(* ------------------------------------------------------------------------- *)

fun lcfrefute fm n cont =
  let val sl = skolemfuns fm
      fun find_skolem fm =
           tryfind(fn (f,t) => tsubst(form_match (f,fm) undefined) t) sl
  in
  lcftab find_skolem ([fm],[],n) cont (undefined,[],0)
  end;

(* ------------------------------------------------------------------------- *)
(* A quick demo before doing deskolemization.                                *)
(* ------------------------------------------------------------------------- *)

fun mk_skol (Forall(y,p),fx) q =
  Imp(Imp(subst (y |==> fx) p,Forall(y,p)),q);

fun simpcont thp (env,sks,k) =
  let val ifn = tsubst(solve env) in
  thp(ifn,onformula ifn (itlist mk_skol sks False))
  end;

lcfrefute (<<"p(1) /\\ ~q(1) /\\ (forall x. p(x) ==> q(x))">>) 1 simpcont;

lcfrefute (<<"(exists x. ~p(x)) /\\ (forall x. p(x))">>) 1 simpcont;


(* ------------------------------------------------------------------------- *)
(*         |- (p(v) ==> forall x. p(x)) ==> q                                *)
(*       -------------------------------------- elim_skolemvar               *)
(*                   |- q                                                    *)
(* ------------------------------------------------------------------------- *)

fun elim_skolemvar th =
  case concl th of
    Imp(Imp(pv,(apx as Forall(x,px))),q) =>
        let val [th1,th2] = List.map (imp_trans(imp_add_concl False th))
                            (imp_false_conseqs pv apx)
            val v = hd(subtract_str (fv pv) (fv apx) @ [x])
            val th3 = gen_right v th1
            val th4 = imp_trans th3 (alpha x (consequent(concl th3))) in
        modusponens (axiom_doubleneg q) (right_mp th2 th4)
        end
  | _ => raise Fail "elim_skolemvar";

(* ------------------------------------------------------------------------- *)
(* Top continuation with careful sorting and variable replacement.           *)
(* Also need to delete post-instantiation duplicates! This shows up more     *)
(* often now that we have adequate sharing.                                  *)
(* ------------------------------------------------------------------------- *)

fun deskolcont thp (env,sks,k) =
  let val ifn = tsubst(solve env)
      val isk = setify_ftp(List.map (fn (p,t) => (onformula ifn p,ifn t)) sks)
      val ssk = sort (decreasing (termsize o snd)) isk
      val vs  = List.map (fn i => Var("Y_"^Int.toString i)) (1--List.length ssk)
      val vfn = replacet(itlist2 (fn (p,t) => fn v => t |---> v) ssk vs undefined)
      val th = thp(vfn o ifn,onformula vfn (itlist mk_skol ssk False)) in
  repeat (elim_skolemvar o imp_swap) th
  end;

(* ------------------------------------------------------------------------- *)
(* Overall first-order prover.                                               *)
(* ------------------------------------------------------------------------- *)

fun lcffol fm =
  let val fvs = fv fm
      val fm' = Imp(itlist mk_forall fvs fm,False)
      val th1 = deepen (fn n => lcfrefute fm' n deskolcont) 0
      val th2 = modusponens (axiom_doubleneg (negatef fm')) th1 in
  itlist (fn v => spec(Var v)) (rev fvs) th2
  end;

(* ------------------------------------------------------------------------- *)
(* Examples in the text.                                                     *)
(* ------------------------------------------------------------------------- *)


START_INTERACTIVE;
val p58 = lcffol
 (<<("forall x. exists v. exists w. forall y. forall z. " ^
    "((P(x) /\\ Q(y)) ==> ((P(v) \\/ R(w))  /\\ (R(z) ==> Q(v))))")>>);

val ewd1062_1 = lcffol
 (<<("(forall x. x <= x) /\\ " ^
   "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
   "(forall x y. f(x) <= y <=> x <= g(y)) " ^
   "==> (forall x y. x <= y ==> f(x) <= f(y))")>>);
END_INTERACTIVE;

(* ------------------------------------------------------------------------- *)
(* More exhaustive set of tests not in the main text.                        *)
(* ------------------------------------------------------------------------- *)


START_INTERACTIVE;

val start_time = Time.toReal (Timer.checkRealTimer (Timer.totalRealTimer ())) ;

val p1 = time lcftaut
 (<<"p ==> q <=> ~q ==> ~p">>);

val p2 = time lcftaut
 (<<"~ ~p <=> p">>);

val p3 = time lcftaut
 (<<"~(p ==> q) ==> q ==> p">>);

val p4 = time lcftaut
 (<<"~p ==> q <=> ~q ==> p">>);

val p5 = time lcftaut
 (<<"(p \\/ q ==> p \\/ r) ==> p \\/ (q ==> r)">>);

val p6 = time lcftaut
 (<<"p \\/ ~p">>);

val p7 = time lcftaut
 (<<"p \\/ ~ ~ ~p">>);

val p8 = time lcftaut
 (<<"((p ==> q) ==> p) ==> p">>);

val p9 = time lcftaut
 (<<"(p \\/ q) /\\ (~p \\/ q) /\\ (p \\/ ~q) ==> ~(~q \\/ ~q)">>);

val p10 = time lcftaut
 (<<"(q ==> r) /\\ (r ==> p /\\ q) /\\ (p ==> q /\\ r) ==> (p <=> q)">>);

val p11 = time lcftaut
 (<<"p <=> p">>);

val p12 = time lcftaut
 (<<"((p <=> q) <=> r) <=> (p <=> (q <=> r))">>);

val p13 = time lcftaut
 (<<"p \\/ q /\\ r <=> (p \\/ q) /\\ (p \\/ r)">>);

val p14 = time lcftaut
 (<<"(p <=> q) <=> (q \\/ ~p) /\\ (~q \\/ p)">>);

val p15 = time lcftaut
 (<<"p ==> q <=> ~p \\/ q">>);

val p16 = time lcftaut
 (<<"(p ==> q) \\/ (q ==> p)">>);

val p17 = time lcftaut
 (<<"p /\\ (q ==> r) ==> s <=> (~p \\/ q \\/ s) /\\ (~p \\/ ~r \\/ s)">>);

val p1 = time lcffol
 (<<"p ==> q <=> ~q ==> ~p">>);

val p2 = time lcffol
 (<<"~ ~p <=> p">>);

val p3 = time lcffol
 (<<"~(p ==> q) ==> q ==> p">>);

val p4 = time lcffol
 (<<"~p ==> q <=> ~q ==> p">>);

val p5 = time lcffol
 (<<"(p \\/ q ==> p \\/ r) ==> p \\/ (q ==> r)">>);

val p6 = time lcffol
 (<<"p \\/ ~p">>);

val p7 = time lcffol
 (<<"p \\/ ~ ~ ~p">>);

val p8 = time lcffol
 (<<"((p ==> q) ==> p) ==> p">>);

val p9 = time lcffol
 (<<"(p \\/ q) /\\ (~p \\/ q) /\\ (p \\/ ~q) ==> ~(~q \\/ ~q)">>);

val p10 = time lcffol
 (<<"(q ==> r) /\\ (r ==> p /\\ q) /\\ (p ==> q /\\ r) ==> (p <=> q)">>);

val p11 = time lcffol
 (<<"p <=> p">>);

val p12 = time lcffol
 (<<"((p <=> q) <=> r) <=> (p <=> (q <=> r))">>);

val p13 = time lcffol
 (<<"p \\/ q /\\ r <=> (p \\/ q) /\\ (p \\/ r)">>);

val p14 = time lcffol
 (<<"(p <=> q) <=> (q \\/ ~p) /\\ (~q \\/ p)">>);

val p15 = time lcffol
 (<<"p ==> q <=> ~p \\/ q">>);

val p16 = time lcffol
 (<<"(p ==> q) \\/ (q ==> p)">>);

val p17 = time lcffol
 (<<"p /\\ (q ==> r) ==> s <=> (~p \\/ q \\/ s) /\\ (~p \\/ ~r \\/ s)">>);

val p18 = time lcffol
 (<<"exists y. forall x. P(y) ==> P(x)">>);

val p19 = time lcffol
 (<<"exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)">>);

val p20 = time lcffol
 (<<("(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) " ^
   "==> (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))")>>);

val p21 = time lcffol
 (<<("(exists x. P ==> Q(x)) /\\ (exists x. Q(x) ==> P) " ^
   "==> (exists x. P <=> Q(x))")>>);

val p22 = time lcffol
 (<<"(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))">>);

val p23 = time lcffol
 (<<"(forall x. P \\/ Q(x)) <=> P \\/ (forall x. Q(x))">>);

val p24 = time lcffol
 (<<("~(exists x. U(x) /\\ Q(x)) /\\ " ^
   "(forall x. P(x) ==> Q(x) \\/ R(x)) /\\ " ^
   "~(exists x. P(x) ==> (exists x. Q(x))) /\\ " ^
   "(forall x. Q(x) /\\ R(x) ==> U(x)) ==> " ^
   "(exists x. P(x) /\\ R(x))")>>);

val p25 = time lcffol
 (<<("(exists x. P(x)) /\\ " ^
   "(forall x. U(x) ==> ~G(x) /\\ R(x)) /\\ " ^
   "(forall x. P(x) ==> G(x) /\\ U(x)) /\\ " ^
   "((forall x. P(x) ==> Q(x)) \\/ (exists x. Q(x) /\\ P(x))) " ^
   "==> (exists x. Q(x) /\\ P(x))")>>);

val p26 = time lcffol
 (<<("((exists x. P(x)) <=> (exists x. Q(x))) /\\ " ^
   "(forall x y. P(x) /\\ Q(y) ==> (R(x) <=> U(y))) " ^
   "==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))")>>);

val p27 = time lcffol
 (<<("(exists x. P(x) /\\ ~Q(x)) /\\ " ^
   "(forall x. P(x) ==> R(x)) /\\ " ^
   "(forall x. U(x) /\\ V(x) ==> P(x)) /\\ " ^
   "(exists x. R(x) /\\ ~Q(x)) " ^
   "==> (forall x. V(x) ==> ~R(x)) " ^
       "==> (forall x. U(x) ==> ~V(x))")>>);

val p28 = time lcffol
 (<<("(forall x. P(x) ==> (forall x. Q(x))) /\\ " ^
   "((forall x. Q(x) \\/ R(x)) ==> (exists x. Q(x) /\\ R(x))) /\\ " ^
   "((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==> " ^
   "(forall x. P(x) /\\ L(x) ==> M(x))")>>);

val p29 = time lcffol
 (<<("(exists x. P(x)) /\\ (exists x. G(x)) ==> " ^
   "((forall x. P(x) ==> H(x)) /\\ (forall x. G(x) ==> J(x)) <=> " ^
    "(forall x y. P(x) /\\ G(y) ==> H(x) /\\ J(y)))")>>);

val p30 = time lcffol
 (<<("(forall x. P(x) \\/ G(x) ==> ~H(x)) /\\ " ^
   "(forall x. (G(x) ==> ~U(x)) ==> P(x) /\\ H(x)) " ^
   "==> (forall x. U(x))")>>);

val p31 = time lcffol
 (<<("~(exists x. P(x) /\\ (G(x) \\/ H(x))) /\\ " ^
   "(exists x. Q(x) /\\ P(x)) /\\ " ^
   "(forall x. ~H(x) ==> J(x)) " ^
   "==> (exists x. Q(x) /\\ J(x))")>>);

val p32 = time lcffol
 (<<("(forall x. P(x) /\\ (G(x) \\/ H(x)) ==> Q(x)) /\\ " ^
   "(forall x. Q(x) /\\ H(x) ==> J(x)) /\\ " ^
   "(forall x. R(x) ==> H(x)) " ^
   "==> (forall x. P(x) /\\ R(x) ==> J(x))")>>);

val p33 = time lcffol
 (<<("(forall x. P(a) /\\ (P(x) ==> P(b)) ==> P(c)) <=> " ^
   "(forall x. P(a) ==> P(x) \\/ P(c)) /\\ (P(a) ==> P(b) ==> P(c))")>>);

(***** NEWLY HARD

val p34 = time lcffol
 (<<("((exists x. forall y. P(x) <=> P(y)) <=> " ^
    "((exists x. Q(x)) <=> (forall y. Q(y)))) <=> " ^
   "((exists x. forall y. Q(x) <=> Q(y)) <=> " ^
    "((exists x. P(x)) <=> (forall y. P(y))))")>>);

 *****)

val p35 = time lcffol
 (<<"exists x y. P(x,y) ==> (forall x y. P(x,y))">>);

val p36 = time lcffol
 (<<("(forall x. exists y. P(x,y)) /\\ " ^
   "(forall x. exists y. G(x,y)) /\\ " ^
   "(forall x y. P(x,y) \\/ G(x,y) " ^
   "==> (forall z. P(y,z) \\/ G(y,z) ==> H(x,z))) " ^
       "==> (forall x. exists y. H(x,y))")>>);

val p37 = time lcffol
 (<<("(forall z. " ^
     "exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\\ P(y,z) /\\ " ^
     "(P(y,w) ==> (exists u. Q(u,w)))) /\\ " ^
   "(forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\\ " ^
   "((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==> " ^
   "(forall x. exists y. R(x,y))")>>);

val p38 = time lcffol
 (<<("(forall x. " ^
     "P(a) /\\ (P(x) ==> (exists y. P(y) /\\ R(x,y))) ==> " ^
     "(exists z w. P(z) /\\ R(x,w) /\\ R(w,z))) <=> " ^
   "(forall x. " ^
     "(~P(a) \\/ P(x) \\/ (exists z w. P(z) /\\ R(x,w) /\\ R(w,z))) /\\ " ^
     "(~P(a) \\/ ~(exists y. P(y) /\\ R(x,y)) \\/ " ^
     "(exists z w. P(z) /\\ R(x,w) /\\ R(w,z))))")>>);

val p39 = time lcffol
 (<<"~(exists x. forall y. P(y,x) <=> ~P(y,y))">>);

val p40 = time lcffol
 (<<("(exists y. forall x. P(x,y) <=> P(x,x)) " ^
  "==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))")>>);

val p41 = time lcffol
 (<<("(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\\ ~P(x,x)) " ^
  "==> ~(exists z. forall x. P(x,z))")>>);


val p42 = time lcffol
 (<<"~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\\ P(z,x)))">>);


(***** SEEMS HARD
val p43 = time lcffol
 (<<("(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) " ^
   "==> forall x y. Q(x,y) <=> Q(y,x)")>>);
 *****)

val p44 = time lcffol
 (<<("(forall x. P(x) ==> (exists y. G(y) /\\ H(x,y)) /\\ " ^
   "(exists y. G(y) /\\ ~H(x,y))) /\\ " ^
   "(exists x. J(x) /\\ (forall y. G(y) ==> H(x,y))) ==> " ^
   "(exists x. J(x) /\\ ~P(x))")>>);

(**** SEEMS HARD

val p45 = time lcffol
 (<<("(forall x. " ^
     "P(x) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y)) ==> " ^
       "(forall y. G(y) /\\ H(x,y) ==> R(y))) /\\ " ^
   "~(exists y. L(y) /\\ R(y)) /\\ " ^
   "(exists x. P(x) /\\ (forall y. H(x,y) ==> " ^
     "L(y)) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y))) ==> " ^
   "(exists x. P(x) /\\ ~(exists y. G(y) /\\ H(x,y)))")>>);
 ******)

val p55 = time lcffol
 (<<("lives(agatha) /\\ lives(butler) /\\ lives(charles) /\\ " ^
   "(killed(agatha,agatha) \\/ killed(butler,agatha) \\/ " ^
    "killed(charles,agatha)) /\\ " ^
   "(forall x y. killed(x,y) ==> hates(x,y) /\\ ~richer(x,y)) /\\ " ^
   "(forall x. hates(agatha,x) ==> ~hates(charles,x)) /\\ " ^
   "(hates(agatha,agatha) /\\ hates(agatha,charles)) /\\ " ^
   "(forall x. lives(x) /\\ ~richer(x,agatha) ==> hates(butler,x)) /\\ " ^
   "(forall x. hates(agatha,x) ==> hates(butler,x)) /\\ " ^
   "(forall x. ~hates(x,agatha) \\/ ~hates(x,butler) \\/ ~hates(x,charles)) " ^
   "==> killed(agatha,agatha) /\\ " ^
       "~killed(butler,agatha) /\\ " ^
       "~killed(charles,agatha)")>>);

val p57 = time lcffol
 (<<("P(f(a,b),f(b,c)) /\\ " ^
   "P(f(b,c),f(a,c)) /\\ " ^
   "(forall x y z. P(x,y) /\\ P(y,z) ==> P(x,z)) " ^
   "==> P(f(a,b),f(a,c))")>>);

val p58 = time lcffol
 (<<("forall P Q R. forall x. exists v. exists w. forall y. forall z. " ^
    "((P(x) /\\ Q(y)) ==> ((P(v) \\/ R(w))  /\\ (R(z) ==> Q(v))))")>>);

val p59 = time lcffol
 (<<"(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\\ ~P(f(x)))">>);

val p60 = time lcffol
 (<<("forall x. P(x,f(x)) <=> " ^
            "exists y. (forall z. P(z,y) ==> P(z,f(x))) /\\ P(x,y)")>>);

val gilmore_3 = time lcffol
 (<<("exists x. forall y z. " ^
        "((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\\ " ^
        "((F(z,x) ==> G(x)) ==> H(z)) /\\ " ^
        "F(x,y) " ^
        "==> F(z,z)")>>);

val gilmore_4 = time lcffol
 (<<("exists x y. forall z. " ^
        "(F(x,y) ==> F(y,z) /\\ F(z,z)) /\\ " ^
        "(F(x,y) /\\ G(x,y) ==> G(x,z) /\\ G(z,z))")>>);

val gilmore_5 = time lcffol
 (<<("(forall x. exists y. F(x,y) \\/ F(y,x)) /\\ " ^
   "(forall x y. F(y,x) ==> F(y,y)) " ^
   "==> exists z. F(z,z)")>>);

val gilmore_6 = time lcffol
 (<<("forall x. exists y. " ^
        "(exists u. forall v. F(u,x) ==> G(v,u) /\\ G(u,x)) " ^
        "==> (exists u. forall v. F(u,y) ==> G(v,u) /\\ G(u,y)) \\/ " ^
            "(forall u v. exists w. G(v,u) \\/ H(w,y,u) ==> G(u,w))")>>);

val gilmore_7 = time lcffol
 (<<("(forall x. K(x) ==> exists y. L(y) /\\ (F(x,y) ==> G(x,y))) /\\ " ^
   "(exists z. K(z) /\\ forall u. L(u) ==> F(z,u)) " ^
   "==> exists v w. K(v) /\\ L(w) /\\ G(v,w)")>>);

val gilmore_8 = time lcffol
 (<<("exists x. forall y z. " ^
        "((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\\ " ^
        "((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\\ " ^
        "F(x,y) " ^
        "==> F(z,z)")>>);

val gilmore_9 = time lcffol
 (<<("forall x. exists y. forall z. " ^
        "((forall u. exists v. F(y,u,v) /\\ G(y,u) /\\ ~H(y,x)) " ^
          "==> (forall u. exists v. F(x,u,v) /\\ G(z,u) /\\ ~H(x,z)) " ^
          "==> (forall u. exists v. F(x,u,v) /\\ G(y,u) /\\ ~H(x,y))) /\\ " ^
        "((forall u. exists v. F(x,u,v) /\\ G(y,u) /\\ ~H(x,y)) " ^
         "==> ~(forall u. exists v. F(x,u,v) /\\ G(z,u) /\\ ~H(x,z)) " ^
         "==> (forall u. exists v. F(y,u,v) /\\ G(y,u) /\\ ~H(y,x)) /\\ " ^
             "(forall u. exists v. F(z,u,v) /\\ G(y,u) /\\ ~H(z,y)))")>>);

val davis_putnam_example = time lcffol
 (<<("exists x. exists y. forall z. " ^
        "(F(x,y) ==> (F(y,z) /\\ F(z,z))) /\\ " ^
        "((F(x,y) /\\ G(x,y)) ==> (G(x,z) /\\ G(z,z)))")>>);

val ewd1062_1 = time lcffol
 (<<("(forall x. x <= x) /\\ " ^
   "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
   "(forall x y. f(x) <= y <=> x <= g(y)) " ^
   "==> (forall x y. x <= y ==> f(x) <= f(y))")>>);

val ewd1062_2 = time lcffol
 (<<("(forall x. x <= x) /\\ " ^
   "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
   "(forall x y. f(x) <= y <=> x <= g(y)) " ^
   "==> (forall x y. x <= y ==> g(x) <= g(y))")>>);

let val finish_time = Time.toReal (Timer.checkRealTimer (Timer.totalRealTimer ())) in (
  print_string ("Complete CPU time (user): " ^ (Real.toString (Real.- (finish_time,start_time))));
  print_newline()
)
end;

END_INTERACTIVE;
