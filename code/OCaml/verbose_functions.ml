(* ========================================================================= *)
(* Verbose functions used for testing                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

let begin_output () = (print_string ":::"; print_newline ());;
let end_output () = (print_newline (); print_string ";;;"; print_newline ());;

let print_list print_elem es =  (* Inspired by the printing of terms *)
    if es = [] then print_string "[]" else (
    print_string "[";
    open_box 0;
    print_elem (hd es); print_break 0 0;
    map (fun e -> (print_string ","; print_break 0 0 ; print_elem e))
            (tl es);
	close_box ();
    print_string "]")
;;

let print_pair p1 p2 (e1,e2) = (print_string "(";p1 e1;print_string ",";p2 e2; print_string ")");;

let print_bool b = (if b then print_string "true" else print_string "false") ; print_newline ();;

let variant' x ys =
  let res = variant x ys in
  (begin_output (); print_string res; end_output (); res)
  ;;

let subst' x y =
  let res = subst x y in
  (begin_output (); print_fol_formula res; end_output (); res) 
  ;;

let icongruence' a b c d =
  let res = icongruence a b c d in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

let ispec' x y =
  let res = ispec x y in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

let isubst' a b c d =
  let res = isubst a b c d in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

let lex' cs =
  let res = lex cs in
  (begin_output (); print_list print_string res; end_output (); res) 
  ;;

let lcffol' a =
  let res = lcffol a in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

let lcftaut' a =
  let res = lcftaut a in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

(*
termsize s > termsize t;;

|==>
*)

let set_goal' a =
  let res = set_goal a in
  (begin_output (); print_goal res; end_output (); res) 
  ;;
  
let imp_intro_tac' s gs =
  let res = imp_intro_tac s gs in
  (begin_output (); print_goal res; end_output (); res) 
  ;;
  
let conj_intro_tac' gs =
  let res = conj_intro_tac gs in
  (begin_output (); print_goal res; end_output (); res) 
  ;;

(*
funpow 2 (auto_tac by ["ant"]) g2
*)

let extract_thm' g =
  let res = extract_thm g in
  (begin_output (); print_thm res; end_output (); res)
  ;;

let prove' f ts =
  let res = prove f ts in
  (begin_output (); print_thm res; end_output (); res) 
  ;;

let unify_and_apply' ts =
  let res = unify_and_apply ts in
  (begin_output (); print_list (print_pair (print_term 0) (print_term 0)) res ; end_output (); res);;
