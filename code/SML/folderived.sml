(* ========================================================================= *)
(* First-order derived rules in the LCF setup.                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*                         ******                                            *)
(*         ------------------------------------------ eq_sym                 *)
(*                      |- s = t ==> t = s                                   *)
(* ------------------------------------------------------------------------- *)

fun eq_sym s t =
  let val rth = axiom_eqrefl s in
  funpow 2 (fn th => (modusponens (imp_swap th) rth))
           (axiom_predcong "=" [s, s] [t, s])
  end;;

(* ------------------------------------------------------------------------- *)
(* |- s = t ==> t = u ==> s = u.                                             *)
(* ------------------------------------------------------------------------- *)

fun eq_trans s t u =
  let val th1 = axiom_predcong "=" [t, u] [s, u] 
      val th2 = modusponens (imp_swap th1) (axiom_eqrefl u) in
  imp_trans (eq_sym s t) th2
  end;;
  
(* ------------------------------------------------------------------------- *)
(*         ---------------------------- icongruence                          *)
(*          |- s = t ==> tm[s] = tm[t]                                       *)
(* ------------------------------------------------------------------------- *)

fun icongruence s t stm ttm =
  if stm = ttm then add_assum (mk_eq s t) (axiom_eqrefl stm)
  else if stm = s andalso ttm = t then imp_refl (mk_eq s t) else
  case (stm,ttm) of
   (Fn(fs,sa),Fn(ft,ta)) => 
		if fs = ft andalso length sa = length ta then
			let val ths = map2 (icongruence s t) sa ta 
				val ts = List.map (consequent o concl) ths in
			imp_trans_chain ths (axiom_funcong fs (List.map lhs ts) (List.map rhs ts))
			end
		else raise Fail "icongruence: not congruent"
  | _ => raise Fail "icongruence: not congruent";;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
icongruence (<<|"s"|>>) (<<|"t"|>>) (<<|"f(s,g(s,t,s),u,h(h(s)))"|>>)
                            (<<|"f(s,g(t,t,s),u,h(h(t)))"|>>);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* |- (forall x. p ==> q(x)) ==> p ==> (forall x. q(x))                      *)
(* ------------------------------------------------------------------------- *)

fun gen_right_th x p q =
  imp_swap(imp_trans (axiom_impall x p) (imp_swap(axiom_allimp x p q)));;

(* ------------------------------------------------------------------------- *)
(*                       |- p ==> q                                          *)
(*         ------------------------------------- genimp "x"                  *)
(*           |- (forall x. p) ==> (forall x. q)                              *)
(* ------------------------------------------------------------------------- *)

fun genimp x th =
  let val (p,q) = dest_imp(concl th) in
  modusponens (axiom_allimp x p q) (gen x th)
  end;;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q[x] then |- p ==> forall x. q[x]                             *)
(* ------------------------------------------------------------------------- *)

fun gen_right x th =
  let val (p,q) = dest_imp(concl th) in
  modusponens (gen_right_th x p q) (gen x th)
  end;;

(* ------------------------------------------------------------------------- *)
(* |- (forall x. p(x) ==> q) ==> (exists x. p(x)) ==> q                      *)
(* ------------------------------------------------------------------------- *)

fun exists_left_th x p q =
  let val  p' = Imp(p,False) 
      val  q' = Imp(q,False) 
	  val th1 = genimp x (imp_swap(imp_trans_th p q False)) 
	  val th2 = imp_trans th1 (gen_right_th x q' p') 
	  val th3 = imp_swap(imp_trans_th q' (Forall(x,p')) False) 
	  val th4 = imp_trans2 (imp_trans th2 th3) (axiom_doubleneg q) 
	  val th5 = imp_add_concl False (genimp x (iff_imp2 (axiom_not p))) 
	  val th6 = imp_trans (iff_imp1 (axiom_not (Forall(x,Not p)))) th5 
	  val th7 = imp_trans (iff_imp1(axiom_exists x p)) th6 in
  imp_swap(imp_trans th7 (imp_swap th4))
  end;;

(* ------------------------------------------------------------------------- *)
(* If |- p(x) ==> q then |- (exists x. p(x)) ==> q                           *)
(* ------------------------------------------------------------------------- *)

fun exists_left x th =
  let val (p,q) = dest_imp(concl th) in
  modusponens (exists_left_th x p q) (gen x th)
  end;;

(* ------------------------------------------------------------------------- *)
(*    |- x = t ==> p ==> q    [x not in t and not free in q]                 *)
(*  --------------------------------------------------------------- subspec  *)
(*                 |- (forall x. p) ==> q                                    *)
(* ------------------------------------------------------------------------- *)

fun subspec th =
  case concl th of
    Imp(e as Atom(R("=",[Var x,t])),Imp(p,q)) =>
        let val th1 = imp_trans (genimp x (imp_swap th))
                            (exists_left_th x e q) in
        modusponens (imp_swap th1) (axiom_existseq x t)
		end
  | _ => raise Fail "subspec: wrong sort of theorem";;

(* ------------------------------------------------------------------------- *)
(*    |- x = y ==> p[x] ==> q[y]  [x not in FV(q); y not in FV(p) or x == y] *)
(*  --------------------------------------------------------- subalpha       *)
(*                 |- (forall x. p) ==> (forall y. q)                        *)
(* ------------------------------------------------------------------------- *)

fun subalpha th =
   case concl th of
    Imp(Atom(R("=",[Var x,Var y])),Imp(p,q)) =>
        if x = y then genimp x (modusponens th (axiom_eqrefl(Var x)))
        else gen_right y (subspec th)
  | _ => raise Fail "subalpha: wrong sort of theorem";;
  
(* ------------------------------------------------------------------------- *)
(*         ---------------------------------- isubst                         *)
(*            |- s = t ==> p[s] ==> p[t]                                     *)
(* ------------------------------------------------------------------------- *)

fun isubst s t sfm tfm =
  if sfm = tfm then add_assum (mk_eq s t) (imp_refl tfm) else
  case (sfm,tfm) of
    (Atom(R(p,sa)),Atom(R(p',ta))) =>
		if p = p' andalso List.length sa = List.length ta then
			let val ths = map2 (icongruence s t) sa ta
			    val (ls,rs) = unzip (List.map (dest_eq o consequent o concl) ths) in
			imp_trans_chain ths (axiom_predcong p ls rs)
			end
		else
			raise Fail "isubst" (* In OCaml-version this case gives Fail "expand_connective" *)
  | (Imp(sp,sq),Imp(tp,tq)) =>
        let val th1 = imp_trans (eq_sym s t) (isubst t s tp sp)
            val th2 = isubst s t sq tq in
        imp_trans_chain [th1, th2] (imp_mono_th sp tp sq tq)
		end
  | (Forall(x,p),Forall(y,q)) =>
        if x = y then
          imp_trans (gen_right x (isubst s t p q)) (axiom_allimp x p q)
        else
          let val z = Var(variant x (unions_str [fv p, fv q, fvt s, fvt t])) 
              val th1 = isubst (Var x) z p (subst (x |==> z) p)
              val th2 = isubst z (Var y) (subst (y |==> z) q) q 
              val th3 = subalpha th1 
			  val th4 = subalpha th2 
              val th5 = isubst s t (consequent(concl th3))
                               (antecedent(concl th4)) in
          imp_swap (imp_trans2 (imp_trans th3 (imp_swap th5)) th4)
		  end
  | _ =>
        let val sth = iff_imp1(expand_connective sfm)
            val tth = iff_imp2(expand_connective tfm) 
            val th1 = isubst s t (consequent(concl sth))
                             (antecedent(concl tth)) in
        imp_swap(imp_trans sth (imp_swap(imp_trans2 th1 tth)))
		end;;
		

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* -------------------------------------------- alpha "z" <<forall x. p[x]>> *)
(*   |- (forall x. p[x]) ==> (forall z. p'[z])                               *)
(*                                                                           *)
(* [Restriction that z is not free in the initial p[x].]                     *)
(* ------------------------------------------------------------------------- *)

fun alpha z fm =
  case fm of
    Forall(x,p) => let val p' = subst (x |==> Var z) p in
                   subalpha(isubst (Var x) (Var z) p p')
				   end
  | _ => raise Fail "alpha: not a universal formula";;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* -------------------------------- ispec t <<forall x. p[x]>>               *)
(*   |- (forall x. p[x]) ==> p'[t]                                           *)
(* ------------------------------------------------------------------------- *)

fun ispec t fm =
  case fm of
    Forall(x,p) =>
      if mem x (fvt t) then
        let val th = alpha (variant x (union_str (fvt t) (var p))) fm in
        imp_trans th (ispec t (consequent(concl th)))
		end
      else subspec(isubst (Var x) t p (subst (x |==> t) p))
  | _ => raise Fail "ispec: non-universal formula";;

(* ------------------------------------------------------------------------- *)
(* Specialization rule.                                                      *)
(* ------------------------------------------------------------------------- *)


fun spec t th = modusponens (ispec t (concl th)) th;;


(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
ispec (<<|"y"|>>) (<<"forall x y z. x + y + z = z + y + x">>);;

(* ------------------------------------------------------------------------- *)
(* Additional tests not in main text.                                        *)
(* ------------------------------------------------------------------------- *)

isubst (<<|"x + x"|>>) (<<|"2 * x"|>>)
        (<<"x + x = x ==> x = 0">>) (<<"2 * x = x ==> x = 0">>);;

isubst (<<|"x + x"|>>)  (<<|"2 * x"|>>)
       (<<"(x + x = y + y) ==> (y + y + y = x + x + x)">>)
       (<<"2 * x = y + y ==> y + y + y = x + 2 * x">>);;

ispec (<<|"x"|>>) (<<"forall x y z. x + y + z = y + z + z">>) ;;

ispec (<<|"x"|>>) (<<"forall x. x = x">>) ;;

ispec (<<|"w + y + z"|>>) (<<"forall x y z. x + y + z = y + z + z">>) ;;

ispec (<<|"x + y + z"|>>) (<<"forall x y z. x + y + z = y + z + z">>) ;;

ispec (<<|"x + y + z"|>>) (<<"forall x y z. nothing_much">>) ;;

isubst (<<|"x + x"|>>) (<<|"2 * x"|>>)
       (<<"(x + x = y + y) <=> (something \\/ y + y + y = x + x + x)">>) 
	   (<<"(2 * x = y + y) <=> (something \\/ y + y + y = x + x + x)">>);;

isubst (<<|"x + x"|>>)  (<<|"2 * x"|>>)
       (<<"(exists x. x = 2) <=> exists y. y + x + x = y + y + y">>)
       (<<"(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)">>);;

isubst (<<|"x"|>>)  (<<|"y"|>>)
        (<<"(forall z. x = z) <=> (exists x. y < z) /\\ (forall y. y < x)">>)
        (<<"(forall z. y = z) <=> (exists x. y < z) /\\ (forall y'. y' < y)">>);;

(* ------------------------------------------------------------------------- *)
(* The bug is now fixed.                                                     *)
(* ------------------------------------------------------------------------- *)

ispec (<<|"x'"|>>) (<<"forall x x' x''. x + x' + x'' = 0">>);;

ispec (<<|"x''"|>>) (<<"forall x x' x''. x + x' + x'' = 0">>);;

ispec (<<|"x' + x''"|>>) (<<"forall x x' x''. x + x' + x'' = 0">>);;

ispec (<<|"x + x' + x''"|>>) (<<"forall x x' x''. x + x' + x'' = 0">>);;

ispec (<<|"2 * x"|>>) (<<"forall x x'. x + x' = x' + x">>);;

END_INTERACTIVE;;
