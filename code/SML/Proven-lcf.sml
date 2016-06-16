structure Proven :> sig
  type nat
  type fol_thm
  val gen : string -> fol_thm -> fol_thm
  val axiom_or : fol formula -> fol formula -> fol_thm
  val axiom_and : fol formula -> fol formula -> fol_thm
  val axiom_not : fol formula -> fol_thm
  val axiom_true : fol_thm
  val concl : fol_thm -> fol formula
  val modusponens : fol_thm -> fol_thm -> fol_thm
  val axiom_addimp : fol formula -> fol formula -> fol_thm
  val axiom_allimp : string -> fol formula -> fol formula -> fol_thm
  val axiom_eqrefl : term -> fol_thm
  val axiom_exists : string -> fol formula -> fol_thm
  val axiom_impall : string -> fol formula -> fol_thm
  val axiom_impiff : fol formula -> fol formula -> fol_thm
  val axiom_funcong : string -> term list -> term list -> fol_thm
  val axiom_iffimp1 : fol formula -> fol formula -> fol_thm
  val axiom_iffimp2 : fol formula -> fol formula -> fol_thm
  val axiom_existseq : string -> term -> fol_thm
  val axiom_predcong : string -> term list -> term list -> fol_thm
  val axiom_doubleneg : fol formula -> fol_thm
  val axiom_distribimp : fol formula -> fol formula -> fol formula -> fol_thm
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

fun equal_tm () = {equal = equal_tma} : term equal
and equal_tma (Var x1) (Fn (x21, x22)) = false
  | equal_tma (Fn (x21, x22)) (Var x1) = false
  | equal_tma (Fn (x21, x22)) (Fn (y21, y22)) =
    ((x21 : string) = y21) andalso equal_list (equal_tm ()) x22 y22
  | equal_tma (Var x1) (Var y1) = ((x1 : string) = y1);
val equal_tm = equal_tm ();

fun equal_fola (R (x1, x2)) (R (y1, y2)) =
  ((x1 : string) = y1) andalso equal_list equal_tm x2 y2;

val equal_fol = {equal = equal_fola} : fol equal;

datatype nat = Zero_nat | Suc of nat;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype fol_thm = Thm of fol formula;

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun gen x p = let
                val Thm pa = p;
              in
                Thm (Forall (x, pa))
              end;

fun mk_eq u v = Atom (R ("=", [u, v]));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun zip_eq l r = map (fn (a, b) => mk_eq a b) (zip l r);

fun occurs_in_list uu [] = false
  | occurs_in_list s (h :: t) = occurs_in s h orelse occurs_in_list s t
and occurs_in s (Var x) = equal_tma s (Var x)
  | occurs_in s (Fn (i, l)) = equal_tma s (Fn (i, l)) orelse occurs_in_list s l;

fun free_in uu True = false
  | free_in uv False = false
  | free_in u (Atom a) = let
                           val R (_, aa) = a;
                         in
                           occurs_in_list u aa
                         end
  | free_in u (Imp (p, q)) = free_in u p orelse free_in u q
  | free_in u (Iff (p, q)) = free_in u p orelse free_in u q
  | free_in u (And (p, q)) = free_in u p orelse free_in u q
  | free_in u (Or (p, q)) = free_in u p orelse free_in u q
  | free_in u (Not p) = free_in u p
  | free_in u (Exists (x, p)) = not (occurs_in (Var x) u) andalso free_in u p
  | free_in u (Forall (x, p)) = not (occurs_in (Var x) u) andalso free_in u p;

fun gen_length n (x :: xs) = gen_length (Suc n) xs
  | gen_length n [] = n;

fun axiom_or p q = Thm (Iff ((Or (p, q)), (Not (And ((Not p), (Not q))))));

fun axiom_and p q =
  Thm (Iff ((And (p, q)), (Imp ((Imp (p, (Imp (q, False)))), False))));

fun axiom_not p = Thm (Iff ((Not p), (Imp (p, False))));

fun imp_chain [] p = p
  | imp_chain (q :: l) p = Imp (q, (imp_chain l p));

val axiom_true : fol_thm = Thm (Iff (True, (Imp (False, False))));

fun equal_fm A_ (Exists (x91, x92)) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Exists (x91, x92)) = false
  | equal_fm A_ (Not x8) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Not x8) = false
  | equal_fm A_ (Not x8) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (Not x8) = false
  | equal_fm A_ (Or (x71, x72)) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (Not x8) = false
  | equal_fm A_ (Not x8) (Or (x71, x72)) = false
  | equal_fm A_ (And (x61, x62)) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Not x8) = false
  | equal_fm A_ (Not x8) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (And (x61, x62)) = false
  | equal_fm A_ (Iff (x51, x52)) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (Not x8) = false
  | equal_fm A_ (Not x8) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Iff (x51, x52)) = false
  | equal_fm A_ (Imp (x41, x42)) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (Not x8) = false
  | equal_fm A_ (Not x8) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (Imp (x41, x42)) = false
  | equal_fm A_ (Atom x3) (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) (Atom x3) = false
  | equal_fm A_ (Atom x3) (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) (Atom x3) = false
  | equal_fm A_ (Atom x3) (Not x8) = false
  | equal_fm A_ (Not x8) (Atom x3) = false
  | equal_fm A_ (Atom x3) (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) (Atom x3) = false
  | equal_fm A_ (Atom x3) (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) (Atom x3) = false
  | equal_fm A_ (Atom x3) (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) (Atom x3) = false
  | equal_fm A_ (Atom x3) (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) (Atom x3) = false
  | equal_fm A_ False (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) False = false
  | equal_fm A_ False (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) False = false
  | equal_fm A_ False (Not x8) = false
  | equal_fm A_ (Not x8) False = false
  | equal_fm A_ False (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) False = false
  | equal_fm A_ False (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) False = false
  | equal_fm A_ False (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) False = false
  | equal_fm A_ False (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) False = false
  | equal_fm A_ False (Atom x3) = false
  | equal_fm A_ (Atom x3) False = false
  | equal_fm A_ True (Forall (x101, x102)) = false
  | equal_fm A_ (Forall (x101, x102)) True = false
  | equal_fm A_ True (Exists (x91, x92)) = false
  | equal_fm A_ (Exists (x91, x92)) True = false
  | equal_fm A_ True (Not x8) = false
  | equal_fm A_ (Not x8) True = false
  | equal_fm A_ True (Or (x71, x72)) = false
  | equal_fm A_ (Or (x71, x72)) True = false
  | equal_fm A_ True (And (x61, x62)) = false
  | equal_fm A_ (And (x61, x62)) True = false
  | equal_fm A_ True (Iff (x51, x52)) = false
  | equal_fm A_ (Iff (x51, x52)) True = false
  | equal_fm A_ True (Imp (x41, x42)) = false
  | equal_fm A_ (Imp (x41, x42)) True = false
  | equal_fm A_ True (Atom x3) = false
  | equal_fm A_ (Atom x3) True = false
  | equal_fm A_ True False = false
  | equal_fm A_ False True = false
  | equal_fm A_ (Forall (x101, x102)) (Forall (y101, y102)) =
    ((x101 : string) = y101) andalso equal_fm A_ x102 y102
  | equal_fm A_ (Exists (x91, x92)) (Exists (y91, y92)) =
    ((x91 : string) = y91) andalso equal_fm A_ x92 y92
  | equal_fm A_ (Not x8) (Not y8) = equal_fm A_ x8 y8
  | equal_fm A_ (Or (x71, x72)) (Or (y71, y72)) =
    equal_fm A_ x71 y71 andalso equal_fm A_ x72 y72
  | equal_fm A_ (And (x61, x62)) (And (y61, y62)) =
    equal_fm A_ x61 y61 andalso equal_fm A_ x62 y62
  | equal_fm A_ (Iff (x51, x52)) (Iff (y51, y52)) =
    equal_fm A_ x51 y51 andalso equal_fm A_ x52 y52
  | equal_fm A_ (Imp (x41, x42)) (Imp (y41, y42)) =
    equal_fm A_ x41 y41 andalso equal_fm A_ x42 y42
  | equal_fm A_ (Atom x3) (Atom y3) = eq A_ x3 y3
  | equal_fm A_ False False = true
  | equal_fm A_ True True = true;

fun concl (Thm x) = x;

fun modusponens pq p =
  (case concl pq of True => Thm True | False => Thm True | Atom _ => Thm True
    | Imp (pa, q) => let
                       val pb = concl p;
                     in
                       (if equal_fm equal_fol pb pa then Thm q else Thm True)
                     end
    | Iff (_, _) => Thm True | And (_, _) => Thm True | Or (_, _) => Thm True
    | Not _ => Thm True | Exists (_, _) => Thm True
    | Forall (_, _) => Thm True);

fun axiom_addimp p q = Thm (Imp (p, (Imp (q, p))));

fun axiom_allimp x p q =
  Thm (Imp ((Forall (x, (Imp (p, q)))), (Imp ((Forall (x, p)), (Forall (x, q))))));

fun axiom_eqrefl u = Thm (mk_eq u u);

fun axiom_exists x p = Thm (Iff ((Exists (x, p)), (Not (Forall (x, (Not p))))));

fun axiom_impall x p =
  (if not (free_in (Var x) p) then Thm (Imp (p, (Forall (x, p))))
    else Thm True);

fun axiom_impiff p q =
  Thm (Imp ((Imp (p, q)), (Imp ((Imp (q, p)), (Iff (p, q))))));

fun size_list x = gen_length Zero_nat x;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

fun axiom_funcong i l r =
  (if equal_nat (size_list l) (size_list r)
    then Thm (imp_chain (zip_eq l r) (mk_eq (Fn (i, l)) (Fn (i, r))))
    else Thm True);

fun axiom_iffimp1 p q = Thm (Imp ((Iff (p, q)), (Imp (p, q))));

fun axiom_iffimp2 p q = Thm (Imp ((Iff (p, q)), (Imp (q, p))));

fun axiom_existseq x u =
  (if not (occurs_in (Var x) u) then Thm (Exists (x, (mk_eq (Var x) u)))
    else Thm True);

fun axiom_predcong i l r =
  (if equal_nat (size_list l) (size_list r)
    then Thm (imp_chain (zip_eq l r)
               (Imp ((Atom (R (i, l))), (Atom (R (i, r))))))
    else Thm True);

fun axiom_doubleneg p = Thm (Imp ((Imp ((Imp (p, False)), False)), p));

fun axiom_distribimp p q r =
  Thm (Imp ((Imp (p, (Imp (q, r)))), (Imp ((Imp (p, q)), (Imp (p, r))))));

end; (*struct Proven*)
