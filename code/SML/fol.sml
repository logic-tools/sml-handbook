(* ========================================================================= *)
(* Basic stuff for first order logic.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen              *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Terms.                                                                    *)
(* ------------------------------------------------------------------------- *)

datatype term =
    Var of string
  | Fn  of string * term list;;
  
fun t_ord t1 t2 =
	case (t1,t2) of 
	  (Var x1, Var x2 ) => str_ord x1 x2
	| (Var _, _) => 1
	| (_, Var _) => ~1
	| (Fn(f1,tl1),Fn(f2,tl2)) =>
	   case str_ord f1 f2 of
	     0 => tl_ord tl1 tl2
		|n => n
and tl_ord tl1 tl2 =
	case  (tl1,tl2) of
	  ([],[]) => 0
	| ([],_) => 1
	| (_,[]) => ~1
	| (t1::tl1',t2::tl2') =>
		case t_ord t1 t2 of 
	     0 => tl_ord tl1' tl2'
	   | n => n
;;

fun t_hash t = 
    case t of
	  Var x => str_hash x
	| Fn (f,tl) => Word.toIntX(Word.+(Word.*(0wx31,Word.fromInt(str_hash f)), Word.fromInt(list_hash t_hash tl)))
;;

infix 6 |---> (* For terms *)

fun (x |---> y) t = (x |-> y) t t_ord t_hash;;

infix 6 |===> (* For terms *)
fun x |===> y = (x |=> y) t_ord t_hash;;

fun apply_t f = apply t_ord t_hash f;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
Fn("sqrt",[Fn("-",[Fn("1",[]),
                   Fn("power",[Fn("cos",[Fn("+",[Var "x", Var "y"])]),
                               Fn("2",[])])])]);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Abbreviation for FOL formula.                                             *)
(* ------------------------------------------------------------------------- *)

datatype fol = (* Predicate *)
    R of string * (term list);;
	
fun fol_ord (r1 as R(s1,tl1)) (r2 as R(s2,tl2)) =
	case str_ord s1 s2 of
	  0 => tl_ord tl1 tl2
	| n => n
;;

fun folfm_ord fm1 fm2 = fm_ord fol_ord fm1 fm2;;

fun union_folfm s1 s2 = union folfm_ord s1 s2;;

fun ftp_ord (fm1,t1) (fm2,t2) =
	case folfm_ord fm1 fm2 of
	  0 => t_ord t1 t2
	| n => n;;
	
fun setify_ftp s = setify ftp_ord s;;

(* ------------------------------------------------------------------------- *)
(* Special case of applying a subfunction to the top *terms*.                *)
(* ------------------------------------------------------------------------- *)

fun onformula f = onatoms(fn (R(p,a)) => Atom(R(p,List.map f a)));;

(* ------------------------------------------------------------------------- *)
(* Trivial example of "x + y < z".                                           *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
Atom(R("<",[Fn("+",[Var "x", Var "y"]), Var "z"]));;
END_INTERACTIVE;;
	
(* ------------------------------------------------------------------------- *)
(* Parsing of terms.                                                         *)
(* ------------------------------------------------------------------------- *)

fun is_const_name s = List.all numeric (explode s) orelse s = "nil";;

fun parse_atomic_term vs inp =
  case inp of
    [] => raise Fail "term expected"
  | "("::rest => parse_bracketed (parse_term vs) ")" rest
  | "-"::rest => papply (fn t => Fn("-",[t])) (parse_atomic_term vs rest)
  | f::"("::")"::rest => (Fn(f,[]),rest)
  | f::"("::rest =>
      papply (fn args => Fn(f,args))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | a::rest =>
      ((if is_const_name a andalso not(mem a vs) then Fn(a,[]) else Var a),rest)

and parse_term vs inp =
  parse_right_infix "::" (fn (e1,e2) => Fn("::",[e1,e2]))
    (parse_right_infix "+" (fn (e1,e2) => Fn("+",[e1,e2]))
       (parse_left_infix "-" (fn (e1,e2) => Fn("-",[e1,e2]))
          (parse_right_infix "*" (fn (e1,e2) => Fn("*",[e1,e2]))
             (parse_left_infix "/" (fn (e1,e2) => Fn("/",[e1,e2]))
                (parse_left_infix "^" (fn (e1,e2) => Fn("^",[e1,e2]))
                   (parse_atomic_term vs)))))) inp;;

val parset = make_parser (parse_term []);;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas.                                                      *)
(* ------------------------------------------------------------------------- *)

fun parse_infix_atom vs inp =       
  let val (tm,rest) = parse_term vs inp in
  if List.exists (nextin rest) ["=", "<", "<=", ">", ">="] then                     
        papply (fn tm' => Atom(R(List.hd rest,[tm,tm'])))                          
               (parse_term vs (List.tl rest))                                       
  else raise Fail ""
  end;;
                                                               
fun parse_atom vs inp =
  (parse_infix_atom vs inp) handle Fail _ =>                                
  case inp of                                                               
    p::"("::")"::rest => (Atom(R(p,[])),rest)                                   
  | p::"("::rest =>
      papply (fn args => Atom(R(p,args)))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | p::rest => 
      if p <> "(" then (Atom(R(p,[])),rest)
	  else raise Fail "parse_atom"
  | _ => raise Fail "parse_atom";;
                                                                               
val parse = make_parser                                                        
  (parse_formula (parse_infix_atom,parse_atom) []);;              

(* ------------------------------------------------------------------------- *)
(* Set up parsing of quotations.                                             *)
(* ------------------------------------------------------------------------- *)

val default_parser = parse;;
datatype default_parser_end = >>;;
fun << s >> = default_parser s;; 

val secondary_parser = parset;;
datatype secondary_parser_end = |>>;;
fun <<| s |>> = secondary_parser s;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<"(forall x. x < 2 ==> 2 * x <= 3) \\/ false">>;;

<<|"2 * x"|>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Printing of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

fun print_term_aux prec fm =
  case fm of
    Var x => print_string x
  | Fn("^",[tm1,tm2]) => print_infix_term_aux true prec 24 "^" tm1 tm2
  | Fn("/",[tm1,tm2]) => print_infix_term_aux true prec 22 " /" tm1 tm2
  | Fn("*",[tm1,tm2]) => print_infix_term_aux false prec 20 " *" tm1 tm2
  | Fn("-",[tm1,tm2]) => print_infix_term_aux true prec 18 " -" tm1 tm2
  | Fn("+",[tm1,tm2]) => print_infix_term_aux false prec 16 " +" tm1 tm2
  | Fn("::",[tm1,tm2]) => print_infix_term_aux false prec 14 "::" tm1 tm2
  | Fn(f,args) => print_fargs_aux f args

and print_fargs_aux f args = (
  print_string f;
  if args = [] then () else
   (print_string "(";
    open_box 0;
    print_term_aux 0 (List.hd args); print_break 0 0;
    List.app (fn t => (print_string ","; print_break 0 0 ; print_term_aux 0 t))
            (List.tl args);
	close_box ();
    print_string ")")
)

and print_infix_term_aux isleft oldprec newprec sym p q = (
  if oldprec > newprec then (print_string "("; open_box 0) else ();
  print_term_aux (if isleft then newprec else newprec+1) p;
  print_string sym;
  print_break (if String.substring (sym, 0, 1) = " " then 1 else 0) 0;
  print_term_aux (if isleft then newprec+1 else newprec) q;
  if oldprec > newprec then (close_box (); print_string ")") else ()
);;

fun print_term prec fm = (print_term_aux prec fm; print_flush ())
and print_fargs f args = (print_fargs_aux f args; print_flush ())
and print_infix_term il op np sym p q = (print_infix_term_aux il op np sym p q; print_flush ());; 

fun printert_aux tm = (
  open_box 0; print_string "<<|";
  open_box 0; print_term_aux 0 tm; close_box();
  print_string "|>>"; close_box()
);;

fun printert tm = (printert_aux tm; print_flush ());;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas.                                                     *)
(* ------------------------------------------------------------------------- *)
	
fun print_atom_aux prec (R (p, args)) =
    if mem p ["=", "<", "<=", ">", ">="] andalso List.length args = 2 then
        print_infix_term_aux false 12 12 (" " ^ p) (List.nth (args, 0)) (List.nth (args, 1))
    else
        print_fargs_aux p args;;
		
fun print_atom prec rpa = (print_atom_aux prec rpa; print_flush ());;
		
val print_fol_formula_aux = print_qformula_aux print_atom_aux;;

fun print_fol_formula f = (print_fol_formula_aux f; print_flush ());;

(* ------------------------------------------------------------------------- *)
(* Examples in the main text.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<"forall x y. exists z. x < z /\\ y < z">>;;

<<"~(forall x. P(x)) <=> exists y. ~P(y)">>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Semantics, implemented of course for finite domains only.                 *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Examples of particular interpretations.                                   *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Free variables in terms and formulas.                                     *)
(* ------------------------------------------------------------------------- *)

fun fvt tm =
    case tm of
      Var x => [x]
    | Fn (f, args) =>
        unions_str (List.map fvt args)
;;

fun var fm =
    case fm of
      False => []
    | True => []
    | Atom (R (p, args)) =>
        unions str_ord (List.map fvt args)
    | Not p => var p
    | And (p, q) => union_str (var p) (var q)
    | Or  (p, q) => union_str (var p) (var q)
    | Imp (p, q) => union_str (var p) (var q)
    | Iff (p, q) => union_str (var p) (var q)
    | Forall (x, p) => insert_str x (var p)
    | Exists (x, p) => insert_str x (var p)
;;

fun fv fm =
    case fm of
      False => []
    | True => []
    | Atom (R (p, args)) =>
        unions_str (List.map fvt args)
    | Not p => fv p
    | And (p, q) => union_str (fv p) (fv q)
    | Or  (p, q) => union_str (fv p) (fv q)
    | Imp (p, q) => union_str (fv p) (fv q)
    | Iff (p, q) => union_str (fv p) (fv q)
    | Forall (x, p) => subtract_str (fv p) [x]
    | Exists (x, p) => subtract_str (fv p) [x]
;;    

(* ------------------------------------------------------------------------- *)
(* Substitution within terms.                                                *)
(* ------------------------------------------------------------------------- *)

fun tsubst sfn tm =
  case tm of
    Var x => tryapplyd_str sfn x tm
  | Fn(f,args) => Fn(f,List.map (tsubst sfn) args);;
  
(* ------------------------------------------------------------------------- *)
(* Variant function and examples.                                            *)
(* ------------------------------------------------------------------------- *)

fun variant x vars =
  if mem x vars then variant (x^"'") vars else x;;
  
START_INTERACTIVE;;
variant "x" ["y", "z"];;

variant "x" ["x", "y"];;

variant "x" ["x", "x'"];;
END_INTERACTIVE;;

(* pg. 134 *)
(* ------------------------------------------------------------------------- *)
(* Substitution in formulas, with variable renaming.                         *)
(* ------------------------------------------------------------------------- *)

fun subst subfn fm =
    case fm of
      False => False
    | True => True
    | Atom (R (p, args)) =>
        Atom (R (p, List.map (tsubst subfn) args))
    | Not p =>
        Not (subst subfn p)
    | And (p, q) =>
        And (subst subfn p, subst subfn q)
    | Or (p, q) =>
        Or  (subst subfn p, subst subfn q)
    | Imp (p, q) =>
        Imp (subst subfn p, subst subfn q)
    | Iff (p, q) =>
        Iff (subst subfn p, subst subfn q)
    | Forall (x, p) =>
        substq subfn mk_forall x p
    | Exists (x, p) =>
        substq subfn mk_exists x p
and substq subfn quant x p =
    let val x' =
        if List.exists (fn y => mem x (fvt (tryapplyd_str subfn y (Var y)))) (subtract_str (fv p) [x]) then
            variant x (fv (subst (undefine_str x subfn) p)) 
        else x
	in
    quant x' (subst ((x |--> Var x') subfn) p)
	end
;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
subst ("y" |==> Var "x") (<<"forall x. x = y">>);;

subst ("y" |==> Var "x") (<<"forall x x'. x = y ==> x = x'">>);;
END_INTERACTIVE;;
