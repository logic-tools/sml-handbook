(* ========================================================================= *)
(* Goals, LCF-like tactics and Mizar-like proofs.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

datatype goals =
  Goals of ((string * fol formula) list * fol formula)list *
           (thm list -> thm);

(* ------------------------------------------------------------------------- *)
(* Printer for goals (just shows first goal plus total number).              *)
(* ------------------------------------------------------------------------- *)

val print_goal_aux =
    let fun print_hyp (l, fm) = (
        open_hbox();
        print_string (l^":");
        print_space ();
        print_formula_aux print_atom_aux fm;
        print_newline();
        close_box()
    ) in
    fn (Goals (gls, jfn)) =>
        case gls of
          [] =>
            print_string "No subgoals"
        | (asl, w) :: ogls =>(
            print_newline ();
            if ogls = [] then
                print_string "1 subgoal:"
            else (
                print_int (List.length gls);
                print_string " subgoals starting with"
            )
            ;
            print_newline();
            List.app print_hyp (List.rev asl);
            print_string "---> ";
            open_hvbox 0; print_formula_aux print_atom_aux w; close_box();
            print_newline ()
          )
    end;

fun print_goal g = (print_goal_aux g; print_flush ());

(* ------------------------------------------------------------------------- *)
(* Setting up goals and terminating them in a theorem.                       *)
(* ------------------------------------------------------------------------- *)

fun set_goal p =
  let fun chk th = if concl th = p then th else raise Fail "wrong theorem" in
  Goals([([],p)],fn [th] => chk(modusponens th truth))
  end;

fun extract_thm gls =
  case gls of
    Goals([],jfn) => jfn []
  | _ => raise Fail "extract_thm: unsolved goals";

fun tac_proof g prf = extract_thm(itlist (fn f => f) (List.rev prf) g);


fun prove p prf = tac_proof (set_goal p) prf;

(* ------------------------------------------------------------------------- *)
(* Conjunction introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

fun conj_intro_tac (Goals((asl,And(p,q))::gls,jfn)) =
  let fun jfn' (thp::thq::ths) =
    jfn(imp_trans_chain [thp, thq] (and_pair p q)::ths) in
  Goals((asl,p)::(asl,q)::gls,jfn')
  end;


(* ------------------------------------------------------------------------- *)
(* Handy idiom for tactic that does not split subgoals.                      *)
(* ------------------------------------------------------------------------- *)

fun jmodify jfn tfn (th::oths) = jfn(tfn th :: oths);

(* ------------------------------------------------------------------------- *)
(* Version of gen_right with a bound variable change.                        *)
(* ------------------------------------------------------------------------- *)

fun gen_right_alpha y x th =
  let val th1 = gen_right y th in
  imp_trans th1 (alpha x (consequent(concl th1)))
  end;

(* ------------------------------------------------------------------------- *)
(* Universal introduction.                                                   *)
(* ------------------------------------------------------------------------- *)

fun forall_intro_tac y (Goals((asl,(fm as Forall(x,p)))::gls,jfn)) =
  if mem y (fv fm) orelse List.exists (mem y o fv o snd) asl
  then raise Fail "fix: variable already free in goal" else
  Goals((asl,subst(x |==> Var y) p)::gls,
        jmodify jfn (gen_right_alpha y x));

(* ------------------------------------------------------------------------- *)
(* Another inference rule: |- P[t] ==> exists x. P[x]                        *)
(* ------------------------------------------------------------------------- *)

fun right_exists x t p =
  let val th = contrapos(ispec t (Forall(x,Not p)))
      val Not(Not p') = antecedent(concl th) in
  end_itlist imp_trans
   [imp_contr p' False, imp_add_concl False (iff_imp1 (axiom_not p')),
    iff_imp2(axiom_not (Not p')), th, iff_imp2(axiom_exists x p)]
  end;

(* ------------------------------------------------------------------------- *)
(* Existential introduction.                                                 *)
(* ------------------------------------------------------------------------- *)

fun exists_intro_tac t (Goals((asl,Exists(x,p))::gls,jfn)) =
  Goals((asl,subst(x |==> t) p)::gls,
        jmodify jfn (fn th => imp_trans th (right_exists x t p))) ;

(* ------------------------------------------------------------------------- *)
(* Implication introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

fun imp_intro_tac s (Goals((asl,Imp(p,q))::gls,jfn)) =
  let val jmod = if asl = [] then add_assum True else imp_swap o shunt in
  Goals(((s,p)::asl,q)::gls,jmodify jfn jmod)
  end;

(* ------------------------------------------------------------------------- *)
(* Append contextual hypothesis to unconditional theorem.                    *)
(* ------------------------------------------------------------------------- *)

fun assumptate (Goals((asl,w)::gls,jfn)) th =
  add_assum (list_conj (map snd asl)) th;

(* ------------------------------------------------------------------------- *)
(* Get the first assumption (quicker than head of assumps result).           *)
(* ------------------------------------------------------------------------- *)

fun firstassum asl =
  let val p = snd(hd asl)
      val q = list_conj(List.map snd (List.tl asl)) in
  if tl asl = [] then imp_refl p else and_left p q
  end;

(* ------------------------------------------------------------------------- *)
(* Import "external" theorem.                                                *)
(* ------------------------------------------------------------------------- *)

fun using ths p g =
  let val ths' = map (fn th => itlist gen (fv(concl th)) th) ths in
  List.map (assumptate g) ths'
  end;

(* ------------------------------------------------------------------------- *)
(* Turn assumptions p1,...,pn into theorems |- p1 /\ ... /\ pn ==> pi        *)
(* ------------------------------------------------------------------------- *)

fun assumps asl =
  case asl of
    [] => []
  | [(l,p)] => [(l,imp_refl p)]
  | (l,p)::lps =>
        let val ths = assumps lps
            val q = antecedent(concl(snd(List.hd ths)))
            val rth = and_right p q in
        (l,and_left p q)::List.map (fn (l,th) => (l,imp_trans rth th)) ths
        end;

(* ------------------------------------------------------------------------- *)
(* Produce canonical theorem from list of theorems or assumption labels.     *)
(* ------------------------------------------------------------------------- *)

fun by hyps p (Goals((asl,w)::gls,jfn)) =
  let val ths = assumps asl in
  List.map (fn s => assoc s ths) hyps
  end;

(* ------------------------------------------------------------------------- *)
(* Main automatic justification step.                                        *)
(* ------------------------------------------------------------------------- *)

local
  fun singleton [_] = true
    | singleton _ = false
in
  fun justify byfn hyps p g =
    let val ths = byfn hyps p g in
    if singleton ths andalso consequent(concl (List.hd ths)) = p then (
      List.hd ths
    ) else (
      let val th = lcffol(itlist (mk_imp o consequent o concl) ths p) in
      case ths of
        [] => assumptate g th
      | _  => imp_trans_chain ths th
      end
    )
    end
end;


(* ------------------------------------------------------------------------- *)
(* Nested subproof.                                                          *)
(* ------------------------------------------------------------------------- *)

fun proof tacs p (Goals((asl,w)::gls,jfn)) =
  [tac_proof (Goals([(asl,p)],fn [th] => th)) tacs];

(* ------------------------------------------------------------------------- *)
(* Trivial justification, producing no hypotheses.                           *)
(* ------------------------------------------------------------------------- *)

fun at once p gl = [];
val once = [];

(* ------------------------------------------------------------------------- *)
(* Hence an automated terminal tactic.                                       *)
(* ------------------------------------------------------------------------- *)

fun auto_tac byfn hyps (g as Goals((asl,w)::gls,jfn)) =
  let val th = justify byfn hyps w g in
  Goals(gls,fn ths => jfn(th::ths))
  end;

(* ------------------------------------------------------------------------- *)
(* A "lemma" tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

fun lemma_tac s p byfn hyps (g as Goals((asl,w)::gls,jfn)) =
  let val tr  = imp_trans(justify byfn hyps p g)
      val mfn = if asl = [] then tr else imp_unduplicate o tr o shunt in
  Goals(((s,p)::asl,w)::gls,jmodify jfn mfn)
  end;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for existential quantification.                        *)
(* ------------------------------------------------------------------------- *)

fun exists_elim_tac l fm byfn hyps (g as Goals((asl,w)::gls,jfn)) =
  let val Exists(x,p) = fm in
  if List.exists (mem x o fv) (w::List.map snd asl)
  then raise Fail "exists_elim_tac: variable free in assumptions" else
  let val th = justify byfn hyps (Exists(x,p)) g
      fun jfn' pth = imp_unduplicate(imp_trans th (exists_left x (shunt pth)))
  in
  Goals(((l,p)::asl,w)::gls,jmodify jfn jfn')
  end end;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> r and |- q ==> r then |- p \/ q ==> r                         *)
(* ------------------------------------------------------------------------- *)

fun ante_disj th1 th2 =
  let val (p,r) = dest_imp(concl th1)
      val (q,s) = dest_imp(concl th2)
      val ths = map contrapos [th1, th2]
      val th3 = imp_trans_chain ths (and_pair (Not p) (Not q))
      val th4 = contrapos(imp_trans (iff_imp2(axiom_not r)) th3)
      val th5 = imp_trans (iff_imp1(axiom_or p q)) th4 in
  right_doubleneg(imp_trans th5 (iff_imp1(axiom_not(Imp(r,False)))))
  end;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for disjunction.                                       *)
(* ------------------------------------------------------------------------- *)

fun disj_elim_tac l fm byfn hyps (g as Goals((asl,w)::gls,jfn) ) =
  let val th = justify byfn hyps fm g
      val Or(p,q) = fm
      fun jfn' (pth::qth::ths) =
         let val th1 = imp_trans th (ante_disj (shunt pth) (shunt qth)) in
         jfn(imp_unduplicate th1::ths)
         end
  in
  Goals(((l,p)::asl,w)::((l,q)::asl,w)::gls,jfn')
  end;

(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;
val g0 = set_goal
 (<<("(forall x. x <= x) /\\ " ^
   "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
   "(forall x y. f(x) <= y <=> x <= g(y)) " ^
   "==> (forall x y. x <= y ==> f(x) <= f(y)) /\\ " ^
       "(forall x y. x <= y ==> g(x) <= g(y))")>>);

val g1 = imp_intro_tac "ant" g0;

val g2 = conj_intro_tac g1;

val g3 = funpow 2 (auto_tac by ["ant"]) g2;

extract_thm g3;

(* ------------------------------------------------------------------------- *)
(* All packaged up together.                                                 *)
(* ------------------------------------------------------------------------- *)

prove (<<("(forall x. x <= x) /\\ " ^
        "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
        "(forall x y. f(x) <= y <=> x <= g(y)) " ^
        "==> (forall x y. x <= y ==> f(x) <= f(y)) /\\ " ^
            "(forall x y. x <= y ==> g(x) <= g(y))")>>)
      [imp_intro_tac "ant",
       conj_intro_tac,
       auto_tac by ["ant"],
       auto_tac by ["ant"]];
END_INTERACTIVE;

(* ------------------------------------------------------------------------- *)
(* Declarative proof.                                                        *)
(* ------------------------------------------------------------------------- *)

fun multishunt i th =
  let val th1 = imp_swap(funpow i (imp_swap o shunt) th) in
  imp_swap(funpow (i-1) (unshunt o imp_front 2) th1)
  end;

fun assume lps (Goals((asl,Imp(p,q))::gls,jfn)) =
  if end_itlist mk_and (map snd lps) <> p then raise Fail "assume" else
  let fun jfn' th =
    if asl = [] then add_assum True th  else multishunt (length lps) th in
  Goals((lps@asl,q)::gls,jmodify jfn jfn')
  end;

fun note (l,p) = lemma_tac l p;

fun have p = note("",p);

fun so tac arg byfn =
  tac arg (fn hyps => fn p => fn (gl as Goals((asl,w)::_,_)) =>
                     firstassum asl :: byfn hyps p gl);

val fix = forall_intro_tac;

fun consider (x,p) = exists_elim_tac "" (Exists(x,p));

fun take tm gls = exists_intro_tac tm gls;

fun cases fm byfn hyps g = disj_elim_tac "" fm byfn hyps g;

(* ------------------------------------------------------------------------- *)
(* Thesis modification.                                                      *)
(* ------------------------------------------------------------------------- *)

fun conclude p byfn hyps (gl as Goals((asl,w)::gls,jfn)) =
  let val th = justify byfn hyps p gl in
  if p = w then Goals((asl,True)::gls,jmodify jfn (fn _ => th)) else
  let val (p',q) = dest_and w in
  if p' <> p then raise Fail "conclude: bad conclusion" else
  let fun mfn th' = imp_trans_chain [th, th'] (and_pair p q) in
  Goals((asl,q)::gls,jmodify jfn mfn)
  end end end;

(* ------------------------------------------------------------------------- *)
(* A useful shorthand for solving the whole goal.                            *)
(* ------------------------------------------------------------------------- *)

fun our thesis byfn hyps (gl as Goals((asl,w)::gls,jfn)) =
  conclude w byfn hyps gl;
val thesis = "";

(* ------------------------------------------------------------------------- *)
(* Termination.                                                              *)
(* ------------------------------------------------------------------------- *)

fun qed (gl as Goals((asl,w)::gls,jfn)) =
  if w = True then Goals(gls,fn ths => jfn(assumptate gl truth :: ths))
  else raise Fail "qed: non-trivial goal";


(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;
val ewd954 = prove
 (<<("(forall x y. x <= y <=> x * y = x) /\\ " ^
   "(forall x y. f(x * y) = f(x) * f(y)) " ^
   "==> forall x y. x <= y ==> f(x) <= f(y)")>>)
 [note("eq_sym",<<"forall x y. x = y ==> y = x">>)
    using [eq_sym (<<|"x"|>>) (<<|"y"|>>)],
  note("eq_trans",<<"forall x y z. x = y /\\ y = z ==> x = z">>)
    using [eq_trans (<<|"x"|>>) (<<|"y"|>>) (<<|"z"|>>)],
  note("eq_cong",<<"forall x y. x = y ==> f(x) = f(y)">>)
    using [axiom_funcong "f" [(<<|"x"|>>)] [(<<|"y"|>>)]],
  assume [("le",<<"forall x y. x <= y <=> x * y = x">>),
          ("hom",<<"forall x y. f(x * y) = f(x) * f(y)">>)],
  fix "x", fix "y",
  assume [("xy",<<"x <= y">>)],
  so have (<<"x * y = x">>) by ["le"],
  so have (<<"f(x * y) = f(x)">>) by ["eq_cong"],
  so have (<<"f(x) = f(x * y)">>) by ["eq_sym"],
  so have (<<"f(x) = f(x) * f(y)">>) by ["eq_trans", "hom"],
  so have (<<"f(x) * f(y) = f(x)">>) by ["eq_sym"],
  so conclude (<<"f(x) <= f(y)">>) by ["le"],
  qed];
END_INTERACTIVE;

(* ------------------------------------------------------------------------- *)
(* More examples not in the main text.                                       *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;
prove
 (<<("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) " ^
   "==> exists y. p(f(f(f(f(y)))))")>>)
  [assume [("A",<<"exists x. p(x)">>)],
   assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
   note ("C",<<"forall x. p(x) ==> p(f(f(f(f(x)))))">>)
   proof
    [have (<<"forall x. p(x) ==> p(f(f(x)))">>) by ["B"],
     so conclude (<<"forall x. p(x) ==> p(f(f(f(f(x)))))">>) at once,
     qed],
   consider ("a",<<"p(a)">>) by ["A"],
   take (<<|"a"|>>),
   so conclude (<<"p(f(f(f(f(a)))))">>) by ["C"],
   qed];

(* ------------------------------------------------------------------------- *)
(* Alternative formulation with lemma construct.                             *)
(* ------------------------------------------------------------------------- *)

let fun lemma (s,p) (gl as Goals((asl,w)::gls,jfn)) =
  Goals((asl,p)::((s,p)::asl,w)::gls,
        fn (thp::thw::oths) =>
            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)) in
prove
 (<<("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) " ^
   "==> exists y. p(f(f(f(f(y)))))")>>)
  [assume [("A",<<"exists x. p(x)">>)],
   assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
   lemma ("C",<<"forall x. p(x) ==> p(f(f(f(f(x)))))">>),
     have (<<"forall x. p(x) ==> p(f(f(x)))">>) by ["B"],
     so conclude (<<"forall x. p(x) ==> p(f(f(f(f(x)))))">>) at once,
     qed,
   consider ("a",<<"p(a)">>) by ["A"],
   take (<<|"a"|>>),
   so conclude (<<"p(f(f(f(f(a)))))">>) by ["C"],
   qed]
end;

(* ------------------------------------------------------------------------- *)
(* Running a series of proof steps one by one on goals.                      *)
(* ------------------------------------------------------------------------- *)

fun run prf g = itlist (fn f => f) (List.rev prf) g;

(* ------------------------------------------------------------------------- *)
(* LCF-style interactivity.                                                  *)
(* ------------------------------------------------------------------------- *)

val current_goal = ref[set_goal False];

fun g x = (
  current_goal := [set_goal x];
  List.hd(!current_goal)
);

fun e t = (
  current_goal := (t(List.hd(!current_goal))::(!current_goal));
  List.hd(!current_goal)
);

fun es t = (
  current_goal := (run t (List.hd(!current_goal))::(!current_goal));
  List.hd(!current_goal)
);

fun b() = (
  current_goal := List.tl(!current_goal);
  List.hd(!current_goal)
);

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

prove (<<("p(a) ==> (forall x. p(x) ==> p(f(x))) " ^
        "==> exists y. p(y) /\\ p(f(y))")>>)
      [our thesis at once,
       qed];

prove
 (<<("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) " ^
   "==> exists y. p(f(f(f(f(y)))))")>>)
  [assume [("A",<<"exists x. p(x)">>)],
   assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
   note ("C",<<"forall x. p(x) ==> p(f(f(f(f(x)))))">>) proof
    [have (<<"forall x. p(x) ==> p(f(f(x)))">>) by ["B"],
     so our thesis at once,
     qed],
   consider ("a",<<"p(a)">>) by ["A"],
   take (<<|"a"|>>),
   so our thesis by ["C"],
   qed];

prove (<<("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) " ^
                  "==> exists y. p(y) /\\ p(f(y))")>>)
      [fix "c",
       assume [("A",<<"p(c)">>)],
       assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
       take (<<|"c"|>>),
       conclude (<<"p(c)">>) by ["A"],
       note ("C",<<"p(c) ==> p(f(c))">>) by ["B"],
       so our thesis by ["C", "A"],
       qed];

prove (<<("p(c) ==> (forall x. p(x) ==> p(f(x))) " ^
                  "==> exists y. p(y) /\\ p(f(y))")>>)
      [assume [("A",<<"p(c)">>)],
       assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
       take (<<|"c"|>>),
       conclude (<<"p(c)">>) by ["A"],
       our thesis by ["A", "B"],
       qed];

prove (<<("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) " ^
                  "==> exists y. p(y) /\\ p(f(y))")>>)
      [fix "c",
       assume [("A",<<"p(c)">>)],
       assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
       take (<<|"c"|>>),
       conclude (<<"p(c)">>) by ["A"],
       note ("C",<<"p(c) ==> p(f(c))">>) by ["B"],
       our thesis by ["C", "A"],
       qed];

prove (<<("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) " ^
                  "==> exists y. p(y) /\\ p(f(y))")>>)
      [fix "c",
       assume [("A",<<"p(c)">>)],
       assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
       take (<<|"c"|>>),
       note ("D",<<"p(c)">>) by ["A"],
       note ("C",<<"p(c) ==> p(f(c))">>) by ["B"],
       our thesis by ["C", "A", "D"],
       qed];


prove (<<"(p(a) \\/ p(b)) ==> q ==> exists y. p(y)">>)
  [assume [("A",<<"p(a) \\/ p(b)">>)],
   assume [("",<<"q">>)],
   cases (<<"p(a) \\/ p(b)">>) by ["A"],
     take (<<|"a"|>>),
     so our thesis at once,
     qed,

     take (<<|"b"|>>),
     so our thesis at once,
     qed];

prove
  (<<"(p(a) \\/ p(b)) /\\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))">>)
  [assume [("base",<<"p(a) \\/ p(b)">>),
           ("Step",<<"forall x. p(x) ==> p(f(x))">>)],
   cases (<<"p(a) \\/ p(b)">>) by ["base"],
     so note("A",<<"p(a)">>) at once,
     note ("X",<<"p(a) ==> p(f(a))">>) by ["Step"],
     take (<<|"a"|>>),
     our thesis by ["A", "X"],
     qed,

     take (<<|"b"|>>),
     so our thesis by ["Step"],
     qed];

prove
 (<<"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))">>)
  [assume [("A",<<"exists x. p(x)">>)],
   assume [("B",<<"forall x. p(x) ==> p(f(x))">>)],
   consider ("a",<<"p(a)">>) by ["A"],
   so note ("concl",<<"p(f(a))">>) by ["B"],
   take (<<|"a"|>>),
   our thesis by ["concl"],
   qed];

prove (<<("(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x)) " ^
       "==> (p(a) <=> q(a))")>>)
  [assume [("A",<<"forall x. p(x) ==> q(x)">>)],
   assume [("B",<<"forall x. q(x) ==> p(x)">>)],
   note ("von",<<"p(a) ==> q(a)">>) by ["A"],
   note ("bis",<<"q(a) ==> p(a)">>) by ["B"],
   our thesis by ["von", "bis"],
   qed];

(*** Mizar-like

prove
  (<<"(p(a) \\/ p(b)) /\\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))">>)
  [assume [("A",<<"antecedent">>)],
   note ("Step",<<"forall x. p(x) ==> p(f(x))">>) by ["A"],
   per_cases by ["A"],
     suppose ("base",<<"p(a)">>),
     note ("X",<<"p(a) ==> p(f(a))">>) by ["Step"],
     take (<<|"a"|>>),
     our thesis by ["base", "X"],
     qed,

     suppose ("base",<<"p(b)">>),
     our thesis by ["Step", "base"],
     qed,
   endcase];

*****)

END_INTERACTIVE;

(* ------------------------------------------------------------------------- *)
(* Some amusing efficiency tests versus a "direct" spec.                     *)
(* ------------------------------------------------------------------------- *)

(*****

fun test n = gen "x"

fun double_th th =
  let val tm = concl th in modusponens (modusponens (and_pair tm tm) th) th;

fun testcase n =
  gen "x" (funpow n double_th (lcftaut (<<"p(x) ==> q(1) \\/ p(x)">>)));

fun test n = time (spec (<<|"2"|>>)) (testcase n),
             time (subst ("x" |=> (<<|"2"|>>))) (concl(testcase n)),
             ();

test 10;
test 11;
test 12;
test 13;
test 14;
test 15;

****)
