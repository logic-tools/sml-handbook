(* ========================================================================= *)
(* Used for testing                                                          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

#remove_printer print_fpf;;
#remove_printer print_exp;;
#remove_printer print_prop_formula;;
#remove_printer print_bdd;;
#remove_printer printert;;
#remove_printer print_fol_formula;;
#remove_printer print_thm;;
#remove_printer print_goal;;
#remove_printer printert;;
#remove_printer print_fpf;;

#use "verbose_functions.ml";;

(print_string "********************\n";
print_string "********TEST********\n";
print_string "********************\;");;

START_INTERACTIVE;;
(begin_output ();print_term 0 (Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("power",[Fn("cos",[Fn("+",[Var "x"; Var "y"])]);
                               Fn("2",[])])])])); end_output ());;
END_INTERACTIVE;;

START_INTERACTIVE;;
(begin_output ();print_fol_formula (Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"])));end_output ());;
END_INTERACTIVE;;

START_INTERACTIVE;;
(begin_output ();print_fol_formula <<(forall x. x < 2 ==> 2 * x <= 3) \/ false>>; end_output ());;

(begin_output ();print_term 0 <<|2 * x|>>; end_output ());;
END_INTERACTIVE;;

START_INTERACTIVE;;
(begin_output ();print_fol_formula <<forall x y. exists z. x < z /\ y < z>>; end_output ());;

(begin_output ();print_fol_formula <<~(forall x. P(x)) <=> exists y. ~P(y)>>; end_output ());;
END_INTERACTIVE;;

START_INTERACTIVE;;
variant' "x" ["y"; "z"];;

variant' "x" ["x"; "y"];;

variant' "x" ["x"; "x'"];;
END_INTERACTIVE;;

START_INTERACTIVE;;
subst' ("y" |=> Var "x") <<forall x. x = y>>;;

subst' ("y" |=> Var "x") <<forall x x'. x = y ==> x = x'>>;;
END_INTERACTIVE;;

START_INTERACTIVE;;
icongruence' <<|s|>> <<|t|>> <<|f(s,g(s,t,s),u,h(h(s)))|>>
                            <<|f(s,g(t,t,s),u,h(h(t)))|>>;;
END_INTERACTIVE;;

START_INTERACTIVE;;
ispec' <<|y|>> <<forall x y z. x + y + z = z + y + x>>;;

(* ------------------------------------------------------------------------- *)
(* Additional tests not in main text.                                        *)
(* ------------------------------------------------------------------------- *)

isubst' <<|x + x|>> <<|2 * x|>>
        <<x + x = x ==> x = 0>> <<2 * x = x ==> x = 0>>;;

isubst' <<|x + x|>>  <<|2 * x|>>
       <<(x + x = y + y) ==> (y + y + y = x + x + x)>>
       <<2 * x = y + y ==> y + y + y = x + 2 * x>>;;

ispec' <<|x|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec' <<|x|>> <<forall x. x = x>> ;;

ispec' <<|w + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec' <<|x + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec' <<|x + y + z|>> <<forall x y z. nothing_much>> ;;

isubst' <<|x + x|>> <<|2 * x|>>
       <<(x + x = y + y) <=> (something \/ y + y + y = x + x + x)>>
       <<(2 * x = y + y) <=> (something \/ y + y + y = x + x + x)>>;;

isubst' <<|x + x|>>  <<|2 * x|>>
       <<(exists x. x = 2) <=> exists y. y + x + x = y + y + y>>
       <<(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)>>;;

isubst' <<|x|>>  <<|y|>>
        <<(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)>>
        <<(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)>>;;

(* ------------------------------------------------------------------------- *)
(* The bug is now fixed.                                                     *)
(* ------------------------------------------------------------------------- *)

ispec' <<|x'|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec' <<|x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec' <<|x' + x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec' <<|x + x' + x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec' <<|2 * x|>> <<forall x x'. x + x' = x' + x>>;;

END_INTERACTIVE;;

START_INTERACTIVE;;
lex'(explode "2*((var_1 + x') + 11)");;
lex'(explode "if (*p1-- == *p2++) then f() else g()");;
END_INTERACTIVE;;

START_INTERACTIVE;;
let p58 = lcffol'
 <<forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let ewd1062_1 = lcffol'
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;
END_INTERACTIVE;;

START_INTERACTIVE;;

let start_time = Sys.time();;

let p1 = time lcftaut'
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time lcftaut'
 <<~ ~p <=> p>>;;

let p3 = time lcftaut'
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time lcftaut'
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time lcftaut'
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time lcftaut'
 <<p \/ ~p>>;;

let p7 = time lcftaut'
 <<p \/ ~ ~ ~p>>;;

let p8 = time lcftaut'
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time lcftaut'
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time lcftaut'
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time lcftaut'
 <<p <=> p>>;;

let p12 = time lcftaut'
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time lcftaut'
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time lcftaut'
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time lcftaut'
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time lcftaut'
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time lcftaut'
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p1 = time lcffol'
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time lcffol'
 <<~ ~p <=> p>>;;

let p3 = time lcffol'
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time lcffol'
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time lcffol'
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time lcffol'
 <<p \/ ~p>>;;

let p7 = time lcffol'
 <<p \/ ~ ~ ~p>>;;

let p8 = time lcffol'
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time lcffol'
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time lcffol'
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time lcffol'
 <<p <=> p>>;;

let p12 = time lcffol'
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time lcffol'
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time lcffol'
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time lcffol'
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time lcffol'
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time lcffol'
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p18 = time lcffol'
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time lcffol'
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time lcffol'
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = time lcffol'
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time lcffol'
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time lcffol'
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time lcffol'
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time lcffol'
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
   ==> (exists x. Q(x) /\ P(x))>>;;

let p26 = time lcffol'
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
   ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time lcffol'
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x))
   ==> (forall x. V(x) ==> ~R(x))
       ==> (forall x. U(x) ==> ~V(x))>>;;

let p28 = time lcffol'
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time lcffol'
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time lcffol'
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
   ==> (forall x. U(x))>>;;

let p31 = time lcffol'
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\
   (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x))
   ==> (exists x. Q(x) /\ J(x))>>;;

let p32 = time lcffol'
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time lcffol'
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

(***** NEWLY HARD

let p34 = time lcffol'
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

 *****)

let p35 = time lcffol'
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

let p36 = time lcffol'
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time lcffol'
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time lcffol'
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time lcffol'
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time lcffol'
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time lcffol'
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time lcffol'
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

(***** SEEMS HARD
let p43 = time lcffol'
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;
 *****)

let p44 = time lcffol'
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

(**** SEEMS HARD

let p45 = time lcffol'
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
 ******)

let p55 = time lcffol'
 <<lives(agatha) /\ lives(butler) /\ lives(charles) /\
   (killed(agatha,agatha) \/ killed(butler,agatha) \/
    killed(charles,agatha)) /\
   (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
   (hates(agatha,agatha) /\ hates(agatha,charles)) /\
   (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
   (forall x. hates(agatha,x) ==> hates(butler,x)) /\
   (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
   ==> killed(agatha,agatha) /\
       ~killed(butler,agatha) /\
       ~killed(charles,agatha)>>;;

let p57 = time lcffol'
 <<P(f(a,b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

let p58 = time lcffol'
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time lcffol'
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time lcffol'
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

let gilmore_3 = time lcffol'
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time lcffol'
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time lcffol'
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time lcffol'
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time lcffol'
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time lcffol'
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_9 = time lcffol'
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
         ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
             (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

let davis_putnam_example = time lcffol'
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

let ewd1062_1 = time lcffol'
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;

let ewd1062_2 = time lcffol'
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> g(x) <= g(y))>>;;

let finish_time = Sys.time() in
print_string
 ("Complete CPU time (user): "^
  (string_of_float(finish_time -. start_time)));;
  print_newline();;

END_INTERACTIVE;;

START_INTERACTIVE;;
let s = <<|f(x,x,x)|>> and t = <<|g(x,y)|>>;;
(begin_output ();print_term 0 s; end_output ());;
(begin_output ();print_term 0 t; end_output ());;

(begin_output ();print_bool (termsize s > termsize t); end_output ());;

let i = ("y" |=> <<|f(x,x,x)|>>);;

(begin_output ();print_bool(termsize (tsubst i s) > termsize (tsubst i t)); end_output ());;
END_INTERACTIVE;;


START_INTERACTIVE;;
let g0 = set_goal'
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>;;

let g1 = imp_intro_tac' "ant" g0;;

let g2 = conj_intro_tac' g1;;

let g3 = funpow 2 (auto_tac by ["ant"]) g2;;
(begin_output ();print_goal g3; end_output ());;

extract_thm' g3;;

(* ------------------------------------------------------------------------- *)
(* All packaged up together.                                                 *)
(* ------------------------------------------------------------------------- *)

prove' <<(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
            (forall x y. x <= y ==> g(x) <= g(y))>>
      [imp_intro_tac "ant";
       conj_intro_tac;
       auto_tac by ["ant"];
       auto_tac by ["ant"]];;
END_INTERACTIVE;;

START_INTERACTIVE;;
let ewd954 = prove'
 <<(forall x y. x <= y <=> x * y = x) /\
   (forall x y. f(x * y) = f(x) * f(y))
   ==> forall x y. x <= y ==> f(x) <= f(y)>>
 [note("eq_sym",<<forall x y. x = y ==> y = x>>)
    using [eq_sym <<|x|>> <<|y|>>];
  note("eq_trans",<<forall x y z. x = y /\ y = z ==> x = z>>)
    using [eq_trans <<|x|>> <<|y|>> <<|z|>>];
  note("eq_cong",<<forall x y. x = y ==> f(x) = f(y)>>)
    using [axiom_funcong "f" [<<|x|>>] [<<|y|>>]];
  assume ["le",<<forall x y. x <= y <=> x * y = x>>;
          "hom",<<forall x y. f(x * y) = f(x) * f(y)>>];
  fix "x"; fix "y";
  assume ["xy",<<x <= y>>];
  so have <<x * y = x>> by ["le"];
  so have <<f(x * y) = f(x)>> by ["eq_cong"];
  so have <<f(x) = f(x * y)>> by ["eq_sym"];
  so have <<f(x) = f(x) * f(y)>> by ["eq_trans"; "hom"];
  so have <<f(x) * f(y) = f(x)>> by ["eq_sym"];
  so conclude <<f(x) <= f(y)>> by ["le"];
  qed];;
END_INTERACTIVE;;

START_INTERACTIVE;;
prove'
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   note ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>)
   proof
    [have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so conclude <<forall x. p(x) ==> p(f(f(f(f(x)))))>> at once;
     qed];
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so conclude <<p(f(f(f(f(a)))))>> by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Alternative formulation with lemma construct.                             *)
(* ------------------------------------------------------------------------- *)

let lemma (s,p) (Goals((asl,w)::gls,jfn) as gl) =
  Goals((asl,p)::((s,p)::asl,w)::gls,
        fun (thp::thw::oths) ->
            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)) in
prove'
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   lemma ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>);
     have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so conclude <<forall x. p(x) ==> p(f(f(f(f(x)))))>> at once;
     qed;
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so conclude <<p(f(f(f(f(a)))))>> by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Running a series of proof steps one by one on goals.                      *)
(* ------------------------------------------------------------------------- *)

let run prf g = itlist (fun f -> f) (rev prf) g;;

(* ------------------------------------------------------------------------- *)
(* LCF-style interactivity.                                                  *)
(* ------------------------------------------------------------------------- *)

let current_goal = ref[set_goal False];;

let g x = current_goal := [set_goal x]; hd(!current_goal);;

let e t = current_goal := (t(hd(!current_goal))::(!current_goal));
          hd(!current_goal);;

let es t = current_goal := (run t (hd(!current_goal))::(!current_goal));
           hd(!current_goal);;

let b() = current_goal := tl(!current_goal); hd(!current_goal);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

prove' <<p(a) ==> (forall x. p(x) ==> p(f(x)))
        ==> exists y. p(y) /\ p(f(y))>>
      [our thesis at once;
       qed];;

prove'
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   note ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>) proof
    [have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so our thesis at once;
     qed];
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so our thesis by ["C"];
   qed];;

prove' <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       so our thesis by ["C"; "A"];
       qed];;

prove' <<p(c) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       our thesis by ["A"; "B"];
       qed];;

prove' <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"];
       qed];;

prove' <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       note ("D",<<p(c)>>) by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"; "D"];
       qed];;


prove' <<(p(a) \/ p(b)) ==> q ==> exists y. p(y)>>
  [assume ["A",<<p(a) \/ p(b)>>];
   assume ["",<<q>>];
   cases <<p(a) \/ p(b)>> by ["A"];
     take <<|a|>>;
     so our thesis at once;
     qed;

     take <<|b|>>;
     so our thesis at once;
     qed];;

prove'
  <<(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["base",<<p(a) \/ p(b)>>;
           "Step",<<forall x. p(x) ==> p(f(x))>>];
   cases <<p(a) \/ p(b)>> by ["base"];
     so note("A",<<p(a)>>) at once;
     note ("X",<<p(a) ==> p(f(a))>>) by ["Step"];
     take <<|a|>>;
     our thesis by ["A"; "X"];
     qed;

     take <<|b|>>;
     so our thesis by ["Step"];
     qed];;

prove'
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   consider ("a",<<p(a)>>) by ["A"];
   so note ("concl",<<p(f(a))>>) by ["B"];
   take <<|a|>>;
   our thesis by ["concl"];
   qed];;

prove' <<(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
       ==> (p(a) <=> q(a))>>
  [assume ["A",<<forall x. p(x) ==> q(x)>>];
   assume ["B",<<forall x. q(x) ==> p(x)>>];
   note ("von",<<p(a) ==> q(a)>>) by ["A"];
   note ("bis",<<q(a) ==> p(a)>>) by ["B"];
   our thesis by ["von"; "bis"];
   qed];;

(*** Mizar-like

prove'
  <<(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["A",<<antecedent>>];
   note ("Step",<<forall x. p(x) ==> p(f(x))>>) by ["A"];
   per_cases by ["A"];
     suppose ("base",<<p(a)>>);
     note ("X",<<p(a) ==> p(f(a))>>) by ["Step"];
     take <<|a|>>;
     our thesis by ["base"; "X"];
     qed;

     suppose ("base",<<p(b)>>);
     our thesis by ["Step"; "base"];
     qed;
   endcase];;

*****)

END_INTERACTIVE;;

START_INTERACTIVE;;
unify_and_apply' [<<|f(x,g(y))|>>,<<|f(f(z),w)|>>];;

unify_and_apply' [<<|f(x,y)|>>,<<|f(y,x)|>>];;

(****  unify_and_apply' [<<|f(x,g(y))|>>,<<|f(y,x)|>>];; *****)

unify_and_apply' [<<|x_0|>>,<<|f(x_1,x_1)|>>;
                 <<|x_1|>>,<<|f(x_2,x_2)|>>;
                 <<|x_2|>>,<<|f(x_3,x_3)|>>];;
END_INTERACTIVE;;


START_INTERACTIVE;;
lcftaut' <<(p ==> q) \/ (q ==> p)>>;;

lcftaut' <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

lcftaut' <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;
END_INTERACTIVE;;
