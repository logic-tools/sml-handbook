(*

Copyright (c) 2016, Alexander Birch Jensen, Anders Schlichtkrull, Jørgen Villadsen
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted
provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this list of conditions and
the following disclaimer. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or other materials
provided with the distribution. The names of the copyright holders may not be used to endorse or
promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER
IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

theory Proven imports Main "~~/src/HOL/Library/Code_Char" begin

type_synonym id = String.literal

datatype tm = Var id | Fn id "tm list"

datatype 'a fm = T | F | Atom 'a | Imp "'a fm" "'a fm" | Iff "'a fm" "'a fm" | And "'a fm" "'a fm" |
    Or "'a fm" "'a fm" | Not "'a fm" | Exists id "'a fm" | Forall id "'a fm"

datatype fol = R id "tm list"

datatype fol_thm = Thm (concl: "fol fm")

abbreviation (input) "fail_thm \<equiv> Thm T"

definition mk_eq :: "tm \<Rightarrow> tm \<Rightarrow> fol fm" where
  "mk_eq u v \<equiv> Atom (R (STR ''='') [u, v])"

definition zip_eq :: "tm list \<Rightarrow> tm list \<Rightarrow> fol fm list" where
  "zip_eq l r \<equiv> map (\<lambda>(u, v). mk_eq u v) (zip l r)"

primrec
  imp_chain :: "fol fm list \<Rightarrow> fol fm \<Rightarrow> fol fm"
where
  "imp_chain [] p = p" |
  "imp_chain (q # l) p = Imp q (imp_chain l p)"

primrec
  occurs_in :: "tm \<Rightarrow> tm \<Rightarrow> bool" and
  occurs_in_list :: "tm \<Rightarrow> tm list \<Rightarrow> bool"
where
  "occurs_in s (Var x) = (s = (Var x))" |
  "occurs_in s (Fn i l) = (s = (Fn i l) \<or> occurs_in_list s l)" |
  "occurs_in_list _ [] = False" |
  "occurs_in_list s (h # t) = (occurs_in s h \<or> occurs_in_list s t)"

primrec
  free_in :: "tm \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "free_in _ T = False" |
  "free_in _ F = False" |
  "free_in u (Atom a) = (case a of R _ l \<Rightarrow> occurs_in_list u l)" |
  "free_in u (Imp p q) = (free_in u p \<or> free_in u q)" |
  "free_in u (Iff p q) = (free_in u p \<or> free_in u q)" |
  "free_in u (And p q) = (free_in u p \<or> free_in u q)" |
  "free_in u (Or p q) = (free_in u p \<or> free_in u q)" |
  "free_in u (Not p) = free_in u p" |
  "free_in u (Exists x p) = (\<not>occurs_in (Var x) u \<and> free_in u p)" |
  "free_in u (Forall x p) = (\<not>occurs_in (Var x) u \<and> free_in u p)"

definition modusponens :: "fol_thm \<Rightarrow> fol_thm \<Rightarrow> fol_thm" where
  "modusponens pq p \<equiv> case concl pq of Imp p'' q \<Rightarrow>
      let p' = concl p in if p' = p'' then Thm q else fail_thm | _ \<Rightarrow> fail_thm"

definition gen :: "id \<Rightarrow> fol_thm \<Rightarrow> fol_thm" where
  "gen x p \<equiv> case p of (Thm p') \<Rightarrow> Thm (Forall x p')"

definition axiom_addimp :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_addimp p q \<equiv> Thm (Imp p (Imp q p))"

definition axiom_distribimp :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_distribimp p q r \<equiv> Thm (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r )))"

definition axiom_doubleneg :: "fol fm \<Rightarrow> fol_thm" where
  "axiom_doubleneg p \<equiv> Thm (Imp (Imp (Imp p F) F) p)"

definition axiom_allimp :: "id \<Rightarrow> fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_allimp x p q \<equiv> Thm (Imp (Forall x (Imp p q)) (Imp (Forall x p) (Forall x q)))"

definition axiom_impall :: "id \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_impall x p \<equiv> if \<not>free_in (Var x) p then Thm (Imp p (Forall x p)) else fail_thm"

definition axiom_existseq :: "id \<Rightarrow> tm \<Rightarrow> fol_thm" where
  "axiom_existseq x u \<equiv> if \<not>occurs_in (Var x) u then Thm (Exists x (mk_eq (Var x) u))
      else fail_thm"

definition axiom_eqrefl :: "tm \<Rightarrow> fol_thm" where
  "axiom_eqrefl u \<equiv> Thm (mk_eq u u)"

definition axiom_funcong :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fol_thm" where
  "axiom_funcong i l r \<equiv>  if length l = length r
      then Thm (imp_chain (zip_eq l r) (mk_eq (Fn i l) (Fn i r))) else fail_thm"

definition axiom_predcong :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fol_thm" where
  "axiom_predcong i l r \<equiv> if length l = length r
      then Thm (imp_chain (zip_eq l r) (Imp (Atom (R i l)) (Atom (R i r)))) else fail_thm"

definition axiom_iffimp1 :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_iffimp1 p q \<equiv> Thm (Imp (Iff p q) (Imp p q))"

definition axiom_iffimp2 :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_iffimp2 p q \<equiv> Thm (Imp (Iff p q) (Imp q p))"

definition axiom_impiff :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_impiff p q \<equiv> Thm (Imp (Imp p q) (Imp (Imp q p) (Iff p q)))"

definition axiom_true :: "fol_thm" where
  "axiom_true \<equiv> Thm (Iff T (Imp F F))"

definition axiom_not :: "fol fm \<Rightarrow> fol_thm" where
  "axiom_not p \<equiv> Thm (Iff (Not p) (Imp p F))"

definition axiom_and :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_and p q \<equiv> Thm (Iff (And p q) (Imp (Imp p (Imp q F)) F))"

definition axiom_or :: "fol fm \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_or p q \<equiv> Thm (Iff (Or p q) (Not (And (Not p) (Not q))))"

definition axiom_exists :: "id \<Rightarrow> fol fm \<Rightarrow> fol_thm" where
  "axiom_exists x p \<equiv> Thm (Iff (Exists x p) (Not (Forall x (Not p))))"

(* Code generation *)

code_printing
  type_constructor tm \<rightharpoonup> (SML) "term"
    | constant Var \<rightharpoonup> (SML) "Var _"
    | constant Fn \<rightharpoonup> (SML) "Fn (_, _)"

code_printing
  type_constructor fm \<rightharpoonup> (SML) "_ formula"
    | constant T \<rightharpoonup> (SML) "True"
    | constant F \<rightharpoonup> (SML) "False"
    | constant Atom \<rightharpoonup> (SML) "Atom _"
    | constant Imp \<rightharpoonup> (SML) "Imp (_, _)"
    | constant Iff \<rightharpoonup> (SML) "Iff (_, _)"
    | constant And \<rightharpoonup> (SML) "And (_, _)"
    | constant Or \<rightharpoonup> (SML) "Or (_, _)"
    | constant Not \<rightharpoonup> (SML) "Not _"
    | constant Exists \<rightharpoonup> (SML) "Exists (_, _)"
    | constant Forall \<rightharpoonup> (SML) "Forall (_, _)"

code_printing
  type_constructor fol \<rightharpoonup> (SML) "fol"
    | constant R \<rightharpoonup> (SML) "R (_, _)"

export_code
  modusponens gen axiom_addimp axiom_distribimp axiom_doubleneg axiom_allimp axiom_impall
  axiom_existseq axiom_eqrefl axiom_funcong axiom_predcong axiom_iffimp1 axiom_iffimp2
  axiom_impiff axiom_true axiom_not axiom_and axiom_or axiom_exists concl
  in SML module_name Proven (* file "Proven.sml" *)

(* FOL semantics *)

primrec
  semantics_term :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a" and
  semantics_list :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list"
where
  "semantics_term e _ (Var x) = e x" |
  "semantics_term e f (Fn i l) = f i (semantics_list e f l)" |
  "semantics_list _ _ [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec
  semantics :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fol fm \<Rightarrow> bool"
where
  "semantics _ _ _ T = True" |
  "semantics _ _ _ F = False" |
  "semantics e f g (Atom a) = (case a of R i l \<Rightarrow> if i = STR ''='' \<and> length l = 2
      then (semantics_term e f (hd l) = semantics_term e f (hd (tl l)))
      else g i (semantics_list e f l))" |
  "semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)" |
  "semantics e f g (Iff p q) = (semantics e f g p \<longleftrightarrow> semantics e f g q)" |
  "semantics e f g (And p q) = (semantics e f g p \<and> semantics e f g q)" |
  "semantics e f g (Or p q) = (semantics e f g p \<or> semantics e f g q)" |
  "semantics e f g (Not p) = (\<not>semantics e f g p)" |
  "semantics e f g (Exists x p) = (\<exists>v. semantics (e(x := v)) f g p)" |
  "semantics e f g (Forall x p) = (\<forall>v. semantics (e(x := v)) f g p)"

(* Inductive predicate on proof system *)

inductive
  OK :: "fol fm \<Rightarrow> bool" ("\<turnstile> _" 0)
where
  modusponens:
                    "\<turnstile> concl pq \<Longrightarrow> \<turnstile> concl p \<Longrightarrow> \<turnstile> concl (modusponens pq p)" |
  gen:
                    "\<turnstile> concl p \<Longrightarrow> \<turnstile> concl (gen _ p)" |
  axiom_addimp:
                    "\<turnstile> concl (axiom_addimp _ _)" |
  axiom_distribimp:
                    "\<turnstile> concl (axiom_distribimp _ _ _)" |
  axiom_doubleneg:
                    "\<turnstile> concl (axiom_doubleneg _)" |
  axiom_allimp:
                    "\<turnstile> concl (axiom_allimp _ _ _)" |
  axiom_impall:
                    "\<turnstile> concl (axiom_impall _ _)" |
  axiom_existseq:
                    "\<turnstile> concl (axiom_existseq _ _)" |
  axiom_eqrefl:
                    "\<turnstile> concl (axiom_eqrefl _)" |
  axiom_funcong:
                    "\<turnstile> concl (axiom_funcong _ _ _)" |
  axiom_predcong:
                    "\<turnstile> concl (axiom_predcong _ _ _)" |
  axiom_iffimp1:
                    "\<turnstile> concl (axiom_iffimp1 _ _)" |
  axiom_iffimp2:
                    "\<turnstile> concl (axiom_iffimp2 _ _)" |
  axiom_impiff:
                    "\<turnstile> concl (axiom_impiff _ _)" |
  axiom_true:
                    "\<turnstile> concl axiom_true" |
  axiom_not:
                    "\<turnstile> concl (axiom_not _)" |
  axiom_and:
                    "\<turnstile> concl (axiom_and _ _)" |
  axiom_or:
                    "\<turnstile> concl (axiom_or _ _)" |
  axiom_exists:
                    "\<turnstile> concl (axiom_exists _ _)"

(* Proof examples *)

lemma imp_refl:
  "\<turnstile> Imp p p"
proof -
  have 1: "\<turnstile> concl (Thm (Imp (Imp p (Imp (Imp p p) p)) (Imp (Imp p (Imp p p)) (Imp p p))))"
  using axiom_distribimp axiom_distribimp_def
  by simp

  have 2: "\<turnstile> concl (Thm (Imp p (Imp (Imp p p) p)))"
  using axiom_addimp axiom_addimp_def
  by simp

  have 3: "\<turnstile> concl (Thm (Imp (Imp p (Imp p p)) (Imp p p)))"
  using 1 2 modusponens modusponens_def
  by fastforce

  have 4: "\<turnstile> concl (Thm (Imp p (Imp p p)))"
  using axiom_addimp axiom_addimp_def
  by simp

  have 5: "\<turnstile> concl (Thm (Imp p p))"
  using 3 4 modusponens modusponens_def
  by fastforce

  show ?thesis
  using 5
  by simp
qed

(* Proof about semantics of axioms *)

lemma sem_axiom_addimp:
  "semantics e f g (concl (axiom_addimp p q))"
unfolding axiom_addimp_def
by simp

lemma sem_axiom_distribimp:
  "semantics e f g (concl (axiom_distribimp p q r))"
unfolding axiom_distribimp_def
by simp

lemma sem_axiom_doubleneg:
  "semantics e f g (concl (axiom_doubleneg p))"
unfolding axiom_doubleneg_def
by simp

lemma sem_axiom_allimp:
  "semantics e f g (concl (axiom_allimp x p q))"
unfolding axiom_allimp_def
by simp

lemma map':
  "\<not>occurs_in (Var x) u \<Longrightarrow> semantics_term e f u = semantics_term (e(x := v)) f u"
  "\<not>occurs_in_list (Var x) l \<Longrightarrow> semantics_list e f l = semantics_list (e(x := v)) f l"

by (induct u and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma map:
  "\<not>free_in (Var x) p \<Longrightarrow> semantics e f g p = semantics (e(x := v)) f g p"
proof (induct p arbitrary: e)
  fix a e
  show "\<not>free_in (Var x) (Atom a) \<Longrightarrow> semantics e f g (Atom a) = semantics (e(x := v)) f g (Atom a)"
  by (induct a) (simp, metis Nitpick.size_list_simp(2) One_nat_def Suc_1 hd_Cons_tl map'
      numeral_One numeral_eq_iff occurs_in_list.simps(2) old.nat.distinct(2) eq_num_simps(4))
qed (simp_all, (metis fun_upd_twist fun_upd_upd)+)

lemma sem_axiom_impall:
  "\<not>free_in (Var x) p \<Longrightarrow> semantics e f g (concl (axiom_impall x p))"
unfolding axiom_impall_def
using map
by fastforce

lemma sem_axiom_existseq:
  "\<not>occurs_in (Var x) u \<Longrightarrow> semantics e f g (concl (axiom_existseq x u))"
unfolding axiom_existseq_def mk_eq_def
using map'
by fastforce

lemma sem_axiom_eqrefl:
  "semantics e f g (concl (axiom_eqrefl u))"
unfolding axiom_eqrefl_def mk_eq_def
by simp

lemma sem_imp_chain:
  "semantics e f g (imp_chain l p) = ((\<exists>q \<in> set l. \<not>semantics e f g q) \<or> semantics e f g p)"
by (induct l) simp_all

lemma semantics_list_two_args:
"length l = 2 \<Longrightarrow> l = [ (l ! 0), (l ! 1) ]"
by (metis (no_types) Cons_nth_drop_Suc One_nat_def Suc_1 Suc_length_conv append.simps(1)
    id_take_nth_drop length_0_conv length_greater_0_conv lessI list.sel(3) take_0 zero_not_eq_two)

lemma sem_imp_chain_zip_eq:
  "length l = length r \<Longrightarrow>
      semantics_list e f l \<noteq> semantics_list e f r \<Longrightarrow> semantics e f g (imp_chain (zip_eq l r) p)"
proof -
  assume *: "length l = length r" "semantics_list e f l \<noteq> semantics_list e f r"
  then have "\<exists>n. n < length l \<and> \<not>semantics e f g (mk_eq (l ! n) (r ! n))"
  unfolding mk_eq_def
  by (induct l r rule: list_induct2') fastforce+
  then obtain n where n_p: "n < length l \<and> \<not>semantics e f g (mk_eq (l ! n) (r ! n))"
  by auto
  then have "\<not>semantics e f g ((zip_eq l r) ! n)"
  unfolding zip_eq_def
  using *(1)
  by simp
  then have "\<exists>q \<in> set (zip_eq l r). \<not>semantics e f g q"
  unfolding zip_eq_def
  using *(1) length_map length_zip min_less_iff_conj n_p nth_mem
  by metis
  then show ?thesis
  by (simp add: sem_imp_chain)
qed

lemma sem_axiom_funcong':
  "length l = length r \<Longrightarrow> semantics e f g (imp_chain (zip_eq l r) (mk_eq (Fn i l) (Fn i r)))"
proof (cases)
  assume "semantics_list e f l = semantics_list e f r"
  then have "semantics e f g (mk_eq (Fn i l) (Fn i r))"
  unfolding mk_eq_def
  by simp
  then show ?thesis
  by (simp add: sem_imp_chain)
next
  assume "semantics_list e f l \<noteq> semantics_list e f r" "length l = length r"
  then show ?thesis
  by (simp add: sem_imp_chain_zip_eq)
qed

lemma sem_axiom_funcong:
  "length l = length r \<Longrightarrow> semantics e f g (concl (axiom_funcong i l r))"
unfolding axiom_funcong_def
using sem_axiom_funcong'
by simp

lemma sem_axiom_predcong':
  "length l = length r \<Longrightarrow>
      semantics e f g (imp_chain (zip_eq l r) (Imp (Atom (R i l)) (Atom (R i r))))"
proof (cases)
  assume *: "semantics_list e f l = semantics_list e f r" "length l = length r"
  then show ?thesis
  proof (cases)
    assume **: "i = STR ''=''"
    then show ?thesis
    proof (cases)
      assume ***: "length l = 2"
      then have ****: "length r = 2"
      using *(2)
      by simp
      then have
        "semantics_list e f [l ! 0, l ! 1] = semantics_list e f [r ! 0, r ! 1]"
      using * semantics_list_two_args
      by metis
      then have "semantics e f g
          (Imp (Atom (R (STR ''='') [l ! 0, l ! 1])) (Atom (R (STR ''='') [r ! 0, r ! 1])))"
      by simp
      then have "semantics e f g (Imp (Atom (R (STR ''='') l)) (Atom (R (STR ''='') r)))"
      using *** **** semantics_list_two_args
      by metis
      then show ?thesis
      using **
      by (simp add: sem_imp_chain)
    next
      assume "length l \<noteq> 2"
      then have "length r \<noteq> 2"
      using *(2)
      by simp
      then show ?thesis
      using *
      by (simp add: sem_imp_chain)
    qed
  next
    assume "i \<noteq> STR ''=''"
    then show ?thesis
    using *(1)
    by (simp add: sem_imp_chain)
  qed
next
  assume *: "semantics_list e f l \<noteq> semantics_list e f r" "length l = length r"
  then show ?thesis
  by (simp add: sem_imp_chain_zip_eq)
qed

lemma sem_axiom_predcong:
  "length l = length r \<Longrightarrow> semantics e f g (concl (axiom_predcong i l r))"
unfolding axiom_predcong_def
using sem_axiom_predcong'
by simp

lemma sem_axiom_iffimp1:
  "semantics e f g (concl (axiom_iffimp1 p q))"
unfolding axiom_iffimp1_def
by simp

lemma sem_axiom_iffimp2:
  "semantics e f g (concl (axiom_iffimp2 p q))"
unfolding axiom_iffimp2_def
by simp

lemma sem_axiom_impiff:
  "semantics e f g (concl (axiom_impiff p q))"
unfolding axiom_impiff_def
by fastforce

lemma sem_axiom_true:
  "semantics e f g (concl (axiom_true))"
unfolding axiom_true_def
by simp

lemma sem_axiom_not:
  "semantics e f g (concl (axiom_not p))"
unfolding axiom_not_def
by simp

lemma sem_axiom_and:
  "semantics e f g (concl (axiom_and p q))"
unfolding axiom_and_def
by simp

lemma sem_axiom_or:
  "semantics e f g (concl (axiom_or p q))"
unfolding axiom_or_def
by simp

lemma sem_axiom_exists:
  "semantics e f g (concl (axiom_exists x p))"
unfolding axiom_exists_def
by simp

(* Soundness of proof system *)

theorem soundness:
  "\<turnstile> p \<Longrightarrow> semantics e f g p"
proof (induct arbitrary: e rule: OK.induct)
  fix e pq p
  assume "semantics e f g (concl pq)" "semantics e f g (concl p)" for e
  then show "semantics e f g (concl (modusponens pq p))"
  unfolding modusponens_def
  proof (induct p)
    fix r
    assume "semantics e f g (concl pq)" "semantics e f g (concl (Thm r))" for e
    then show "semantics e f g (concl (case concl pq of Imp p'' q \<Rightarrow>
        let p' = concl (Thm r) in if p' = p'' then Thm q else fail_thm | _ \<Rightarrow> fail_thm))"
    proof (induct pq)
      fix s
      assume "semantics e f g (concl (Thm s))" "semantics e f g (concl (Thm r))" for e
      then show "semantics e f g (concl (case concl (Thm s) of Imp p'' q \<Rightarrow>
          let p' = concl (Thm r) in if p' = p'' then Thm q else fail_thm | _ \<Rightarrow> fail_thm))"
      by (induct s) auto
    qed
  qed
next
  fix e x p
  assume "semantics e f g (concl p)" for e
  then show "semantics e f g (concl (gen x p))"
  unfolding gen_def
  by (induct p) simp
next
  fix e p q
  show "semantics e f g (concl (axiom_addimp p q))"
  using sem_axiom_addimp
  .
next
  fix e p q r
  show "semantics e f g (concl (axiom_distribimp p q r))"
  using sem_axiom_distribimp
  .
next
  fix e g p
  show "semantics e f g (concl (axiom_doubleneg p))"
  using sem_axiom_doubleneg
  .
next
  fix e x p q
  show "semantics e f g (concl (axiom_allimp x p q))"
  using sem_axiom_allimp
  .
next
  fix e p q
  show "semantics e f g (concl (axiom_iffimp1 p q))"
  using sem_axiom_iffimp1
  .
next
  fix e p q
  show "semantics e f g (concl (axiom_iffimp2 p q))"
  using sem_axiom_iffimp2
  .
next
  fix e p q
  show "semantics e f g (concl (axiom_impiff p q))"
  using sem_axiom_impiff
  .
next
  fix e
  show "semantics e f g (concl (axiom_true))"
  using sem_axiom_true
  .
next
  fix e p
  show "semantics e f g (concl (axiom_not p))"
  using sem_axiom_not
  .
next
  fix e p q
  show "semantics e f g (concl (axiom_and p q))"
  using sem_axiom_and
  .
next
  fix e p q
  show "semantics e f g (concl (axiom_or p q))"
  using sem_axiom_or
  .
next
  fix e x p
  show "semantics e f g (concl (axiom_exists x p))"
  using sem_axiom_exists
  .
next
  fix e t
  show "semantics e f g (concl (axiom_eqrefl t))"
  using sem_axiom_eqrefl
  .
next
  fix e x p
  show "semantics e f g (concl (axiom_impall x p))"
  proof (cases)
    assume "free_in (Var x) p"
    then show ?thesis
    unfolding axiom_impall_def
    by simp
  next
    assume "\<not>free_in (Var x) p"
    then show ?thesis
    by (simp add: sem_axiom_impall)
  qed
next
  fix e x t
  show "semantics e f g (concl (axiom_existseq x t))"
  proof (cases)
    assume "occurs_in (Var x) t"
    then show ?thesis
    unfolding axiom_existseq_def
    by simp
  next
    assume "\<not>occurs_in (Var x) t"
    then show ?thesis
    by (simp add: sem_axiom_existseq)
  qed
next
  fix e x l r
  show "semantics e f g (concl (axiom_funcong x l r))"
  proof (cases)
    assume "length l = length r"
    then show ?thesis
    by (simp add: sem_axiom_funcong)
  next
    assume "length l \<noteq> length r"
    then show ?thesis
    unfolding axiom_funcong_def
    by simp
  qed
next
  fix e x l r
  show "semantics e f g (concl (axiom_predcong x l r))"
  proof (cases)
    assume "length l = length r"
    then show ?thesis
    by (simp add: sem_axiom_predcong)
  next
    assume "length l \<noteq> length r"
    then show ?thesis
    unfolding axiom_predcong_def
    by simp
  qed
qed

end
