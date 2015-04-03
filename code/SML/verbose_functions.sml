(* ========================================================================= *)
(* Verbose functions used for testing                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

fun begin_output () = (print_string ":::"; print_newline ());;
fun end_output () = (print_newline (); print_string ";;;"; print_newline ());;

fun print_list print_elem es= ( (* Inspired by the printing of terms *)
    if es = [] then print_string "[]" else (
    print_string "[";
    open_box 0;
    print_elem (List.hd es); print_break 0 0;
    List.app (fn e => (print_string ","; print_break 0 0 ; print_elem e))
            (List.tl es);
	close_box ();
    print_string "]"
));;

fun print_pair p1 p2 (e1,e2) = (print_string "(";p1 e1;print_string ",";p2 e2; print_string ")");;

fun print_bool b = ((if b then print_string "true" else print_string "false"); print_newline ());;

fun variant' x ys =
  let val res = variant x ys in
  (begin_output (); print_string res; end_output (); res) 
  end;;

fun subst' x y =
  let val res = subst x y in
  (begin_output (); print_fol_formula_aux res; end_output (); res)
  end;;

fun icongruence' a b c d =
  let val res = icongruence a b c d in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun ispec' x y =
  let val res = ispec x y in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun isubst' a b c d =
  let val res = isubst a b c d in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun lex' cs =
  let val res = lex cs in
  (begin_output (); print_list print_string res; end_output (); res) 
  end;;

fun lcffol' a =
  let val res = lcffol a in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun lcftaut' a =
  let val res = lcftaut a in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun set_goal' a =
  let val res = set_goal a in
  (begin_output (); print_goal res; end_output (); res) 
  end;;
  
fun imp_intro_tac' s gs =
  let val res = imp_intro_tac s gs in
  (begin_output (); print_goal res; end_output (); res) 
  end;;
  
fun conj_intro_tac' gs =
  let val res = conj_intro_tac gs in
  (begin_output (); print_goal res; end_output (); res) 
  end;;

fun extract_thm' g =
  let val res = extract_thm g in
  (begin_output (); print_thm res; end_output (); res)
  end;;

fun prove' f ts =
  let val res = prove f ts in
  (begin_output (); print_thm res; end_output (); res) 
  end;;

fun unify_and_apply' ts =
  let val res = unify_and_apply ts in
  (begin_output (); print_list (print_pair (print_term_aux 0) (print_term_aux 0)) res ; end_output (); res)
  end;;
