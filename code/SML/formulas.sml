(* ========================================================================= *)
(* Polymorphic type of formulas with parser and printer.                     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

datatype 'a formula =
    False
  | True
  | Atom of 'a
  | Not of 'a formula
  | And of ('a formula) * ('a formula)
  | Or  of ('a formula) * ('a formula)
  | Imp of ('a formula) * ('a formula)
  | Iff of ('a formula) * ('a formula)
  | Forall of string * ('a formula)
  | Exists of string * ('a formula);


fun fm_ord at_ord fm1 fm2 =
    case (fm1,fm2) of
      (False,False) => 0
    | (False,_) =>  1
    | (_,False) => ~1

    | (True,True) => 0
    | (True,_)  =>  1
    | (_,True)  => ~1

    | (Atom a, Atom b) => at_ord a b
    | (Atom(_),_) => 1
    | (_,Atom(_)) => ~1

    | (Not a,Not b) => fm_ord at_ord a b
    | (Not(_),_) => 1
    | (_,Not(_)) => ~1

    | (And(a1,a2),And(b1,b2)) => fm_pair_ord at_ord (a1,a2) (b1,b2)
    | (And(_,_),_) =>  1
    | (_,And(_,_)) => ~1

    | (Or(a1,a2),Or(b1,b2)) => fm_pair_ord at_ord (a1,a2) (b1,b2)
    | (Or(_,_),_) =>  1
    | (_,Or(_,_)) => ~1

    | (Imp(a1,a2),Imp(b1,b2)) => fm_pair_ord at_ord (a1,a2) (b1,b2)
    | (Imp(_,_),_) =>  1
    | (_,Imp(_,_)) => ~1

    | (Iff(a1,a2),Iff(b1,b2)) => fm_pair_ord at_ord (a1,a2) (b1,b2)
    | (Iff(_,_),_) =>  1
    | (_,Iff(_,_)) => ~1

    | (Forall(x1,a),Forall(x2,b)) => fm_quant_ord at_ord (x1,a) (x2,b)
    | (Forall (_,_), _) => 1
    | (_, Forall (_,_)) => ~1

    | (Exists(x1,a),Exists(x2,b)) => fm_quant_ord at_ord (x1,a) (x2,b)
and fm_pair_ord at_ord (a1,a2) (b1,b2) =
    case fm_ord at_ord a1 b1 of
     0 => fm_ord at_ord a2 b2
    |n => n
and fm_quant_ord at_ord (x1,a) (x2,b) =
    case str_ord x1 x2 of
     0 => fm_ord at_ord a b
    |n => n
;

(* ------------------------------------------------------------------------- *)
(* General parsing of iterated infixes.                                      *)
(* ------------------------------------------------------------------------- *)

fun parse_ginfix opsym opupdate sof subparser inp =
  let val (e1,inp1) = subparser inp in
  if inp1 <> [] andalso List.hd inp1 = opsym then
     parse_ginfix opsym opupdate (opupdate sof e1) subparser (List.tl inp1)
  else (sof e1,inp1)
  end;

fun parse_left_infix opsym opcon =
  parse_ginfix opsym (fn f => fn e1 => fn e2 => opcon(f e1,e2)) (fn x => x);

fun parse_right_infix opsym opcon =
  parse_ginfix opsym (fn f => fn e1 => fn e2 => f(opcon(e1,e2))) (fn x => x);

fun parse_list opsym =
  parse_ginfix opsym (fn f => fn e1 => fn e2 => (f e1)@[e2]) (fn x => [x]);

(* ------------------------------------------------------------------------- *)
(* Other general parsing combinators.                                        *)
(* ------------------------------------------------------------------------- *)

fun papply f (ast,rest) = (f ast,rest);

fun nextin inp tok = inp <> [] andalso List.hd inp = tok;

fun parse_bracketed subparser cbra inp =
  let  val(ast,rest) = subparser inp in
  if nextin rest cbra then (ast,List.tl rest)
  else raise Fail "Closing bracket expected"
  end;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas, parametrized by atom parser "pfn".                   *)
(* ------------------------------------------------------------------------- *)

fun parse_atomic_formula (ifn,afn) vs inp =
  case inp of
    [] => raise Fail "formula expected"
  | "false"::rest => (False,rest)
  | "true"::rest => (True,rest)
  | "("::rest => ( (ifn vs inp) handle Fail _ =>
                  parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
  | "~"::rest => papply (fn p => Not p)
                        (parse_atomic_formula (ifn,afn) vs rest)
  | "forall"::x::rest =>
        parse_quant (ifn,afn) (x::vs) (fn (x,p) => Forall(x,p)) x rest
  | "exists"::x::rest =>
        parse_quant (ifn,afn) (x::vs) (fn (x,p) => Exists(x,p)) x rest
  | _ => afn vs inp

and parse_quant (ifn,afn) vs qcon x inp =
   case inp of
     [] => raise Fail "Body of quantified term expected"
   | y::rest =>
        papply (fn fm => qcon(x,fm))
               (if y = "." then parse_formula (ifn,afn) vs rest
                else parse_quant (ifn,afn) (y::vs) qcon y rest)

and parse_formula (ifn,afn) vs inp =
   parse_right_infix "<=>" (fn (p,q) => Iff(p,q))
     (parse_right_infix "==>" (fn (p,q) => Imp(p,q))
         (parse_right_infix "\\/" (fn (p,q) => Or(p,q))
             (parse_right_infix "/\\" (fn (p,q) => And(p,q))
                  (parse_atomic_formula (ifn,afn) vs)))) inp;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas, parametrized by atom printer.                       *)
(* ------------------------------------------------------------------------- *)
(* The OCaml Format lib is not used. *)

fun bracket p n f x y = (
    (if p then print_string "(" else ());
    open_box n; f x y; close_box();
    (if p then print_string ")" else ())
);

fun strip_quant fm =
    case fm of
      Forall (x, (Forall (y, p))) =>
        let val (xs, q) = strip_quant (Forall (y, p)) in
        ((x :: xs), q)
        end
    | Exists (x, (Exists (y, p))) =>
        let val (xs, q) = strip_quant (Exists (y, p)) in
        ((x :: xs), q)
        end
    | Forall (x, p) =>
        ([x],p)
    | Exists (x, p) =>
        ([x],p)
    | _ =>
        ([], fm);

fun print_formula_aux pfn =
    let fun print_formula pr fm =
        case fm of
          False =>
            print_string "false"
        | True =>
            print_string "true"
        | Atom pargs =>
            pfn pr pargs
        | Not p =>
            bracket (pr > 10) 1 (print_prefix 10) "~" p
        | And (p, q) =>
            bracket (pr > 8) 0 (print_infix 8 "/\\") p q
        | Or (p, q) =>
            bracket (pr > 6) 0 (print_infix  6 "\\/") p q
        | Imp (p, q) =>
            bracket (pr > 4) 0 (print_infix 4 "==>") p q
        | Iff (p, q) =>
            bracket (pr > 2) 0 (print_infix 2 "<=>") p q
        | Forall (x, p) =>
            bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
        | Exists (x, p) =>
            bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)

    and print_qnt qname (bvs, bod) = (
        print_string qname;
        List.app (fn v => (print_string " "; print_string v)) bvs;
        print_string "."; print_space(); open_box 0;
        print_formula 0 bod;
        close_box()
    )

    and print_prefix newpr sym p = (
        print_string sym ; print_formula (newpr + 1) p
    )

    and print_infix newpr sym p q = (
        print_formula (newpr + 1) p ;
        print_string (" "^sym); print_space();
        print_formula newpr q
    ) in
    print_formula 0
    end
    ;

fun print_formula pfn fm = (print_formula_aux pfn fm; print_flush ());

fun print_qformula_aux pfn fm = (
  open_box 0; print_string "<<";
  open_box 0; print_formula_aux pfn fm; close_box();
  print_string ">>"; close_box()
);

fun print_qformula pfn fm = (print_qformula_aux pfn fm; print_flush ());

(* ------------------------------------------------------------------------- *)
(* OCaml won't let us use the constructors.                                  *)
(* ------------------------------------------------------------------------- *)

fun mk_and p q = And (p, q)

fun mk_or p q = Or (p, q)

fun mk_imp p q = Imp (p, q)

fun mk_iff p q = Iff (p, q)

fun mk_forall x p = Forall (x, p)

fun mk_exists x p = Exists (x, p)

(* pg. 30 *)
(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

fun dest_iff fm =
  case fm of Iff(p,q) => (p,q) | _ => raise Fail "dest_iff";

fun dest_and fm =
  case fm of And(p,q) => (p,q) | _ => raise Fail ("dest_and");

fun conjuncts fm =
  case fm of And(p,q) => conjuncts p @ conjuncts q | _ => [fm];

fun dest_or fm =
  case fm of Or(p,q) => (p,q) | _ => raise Fail "dest_or";

fun disjuncts fm =
  case fm of Or(p,q) => disjuncts p @ disjuncts q | _ => [fm];

fun dest_imp fm =
  case fm of Imp(p,q) => (p,q) | _ => raise Fail "dest_imp";

fun antecedent fm = fst (dest_imp fm);
fun consequent fm = snd (dest_imp fm);

(* ------------------------------------------------------------------------- *)
(* Apply a function to the atoms, otherwise keeping structure.               *)
(* ------------------------------------------------------------------------- *)

fun onatoms f fm =
  case fm of
    Atom a => f a
  | Not(p) => Not(onatoms f p)
  | And(p,q) => And(onatoms f p,onatoms f q)
  | Or(p,q) => Or(onatoms f p,onatoms f q)
  | Imp(p,q) => Imp(onatoms f p,onatoms f q)
  | Iff(p,q) => Iff(onatoms f p,onatoms f q)
  | Forall(x,p) => Forall(x,onatoms f p)
  | Exists(x,p) => Exists(x,onatoms f p)
  | _ => fm;


(* ------------------------------------------------------------------------- *)
(* Formula analog of list iterator "itlist".                                 *)
(* ------------------------------------------------------------------------- *)

fun overatoms f fm b =
  case fm of
    Atom(a) => f a b
  | Not(p) => overatoms f p b
  | And(p,q) => overatoms f p (overatoms f q b)
  | Or(p,q)  => overatoms f p (overatoms f q b)
  | Imp(p,q) => overatoms f p (overatoms f q b)
  | Iff(p,q) => overatoms f p (overatoms f q b)
  | Forall(x,p) => overatoms f p b
  | Exists(x,p) => overatoms f p b
  | _ => b;

(* ------------------------------------------------------------------------- *)
(* Special case of a union of the results of a function over the atoms.      *)
(* ------------------------------------------------------------------------- *)

fun atom_union ord f fm = setify ord (overatoms (fn h => fn t => f(h)@t) fm []);

fun atom_union_sip f fm = atom_union sip_ord f fm;
