(* ========================================================================= *)
(* Misc library functions to set up a nice environment.                      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison.                                   *)
(* Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen             *)
(* All rights reserved. (See "LICENSE.txt" for details.)                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Implementations of functions not available in SML                         *)
(* ------------------------------------------------------------------------- *)

fun str_ord s1 s2 = 
    case String.compare(s1,s2) of
      EQUAL => 0    | GREATER => 1    | LESS  => ~1;;
      
fun sip_ord (f1,a1) (f2,a2) =
    case str_ord f1 f2 of
      0 => if a1>a2 then 1 else ~1
    | n => n
;;
      
infix 6 lxor 
infix 6 land 

fun to_int_fun f = fn a => fn b => Word.toIntX (f ((Word.fromInt a),(Word.fromInt b) ) );;

fun a lxor b = to_int_fun Word.xorb a b;;
fun a land b = to_int_fun Word.andb a b;;

fun list_hash elem_hash l= (* Inspired by the list hash of Java*)
  let fun hash_code sval l =
        case l of
         [] => sval
        | e::l' => 
          let val e_hash = Word.fromInt (elem_hash e) in
          hash_code (Word.+(Word.*(sval,0wx31),(e_hash))) l'
          end
  in
  Word.toIntX(hash_code 0wx0 l)
  end
;;

fun str_hash str = list_hash Char.ord (String.explode str);; (* Inspired by the string hash of Java*)

fun fst (x,_) = x;; (* Implementation of built-in Ocaml function *)
fun snd (_,y) = y;; (* Implementation of built-in Ocaml function *)

(* ========================================================================= *)
(* Misc library functions to set up a nice environment.                      *)
(* ========================================================================= *)

fun identity x = x;;

(* NOTE: The ( ** ) operator has been replaced with the equivalent built-in sml operator o. *)

(* ------------------------------------------------------------------------- *)
(* GCD and LCM on arbitrary-precision numbers.                               *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* A useful idiom for "non contradictory" etc.                               *)
(* ------------------------------------------------------------------------- *)

fun non p x = not(p x);;

(* ------------------------------------------------------------------------- *)
(* Kind of assertion checking.                                               *)
(* ------------------------------------------------------------------------- *)

fun check p x = if p(x) then x else raise Fail "check";;

(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

fun funpow n f x =
    if n < 1 then x
    else funpow (n - 1) f (f x);;
    
fun can f x = (f x; true) handle Fail _ => false;;

fun repeat f x = repeat f (f x) handle Fail _ => x;;

(* ------------------------------------------------------------------------- *)
(* Handy list operations.                                                    *)
(* ------------------------------------------------------------------------- *)

infix 6 -- (* I am not sure 6 is the right no. *)
fun m -- n = if m > n then [] else m::((m + 1) -- n);;

(* TODO: --- operator *)

fun map2 f l1 l2 =
  case (l1,l2) of
    ([],[]) => []
  | ((h1::t1),(h2::t2)) => let val h = f h1 h2 in h::(map2 f t1 t2) end
  | _ => raise Fail "map2: length mismatch";;

(* NOTE: rev has been replaced with the equivalent built-in SML function List.rev. *)

(* NOTE: hd has been replaced with the equivalent built-in SML function List.hd. *)
        
(* NOTE: tl has been replaced with the equivalent built-in SML function List.tl. *)

fun itlist f l b = List.foldr (fn (x,y) => f x y) b l;; (* Uses SML library *)

fun end_itlist f l =
  case l of
        []     => raise Fail "end_itlist"
      | [x]    => x
      | (h::t) => f h (end_itlist f t);;

fun itlist2 f l1 l2 b = 
  case (l1,l2) of
    ([],[]) => b
  | (h1::t1,h2::t2) => f h1 h2 (itlist2 f t1 t2 b)
  | _ => raise Fail "itlist2";;

fun zip l1 l2 =
  case (l1,l2) of
        ([],[]) => []
      | (h1::t1,h2::t2) => (h1,h2)::(zip t1 t2)
      | _ => raise Fail "zip";;
  
(* NOTE: forall has been replaced with the equivalent built-in SML function List.all. *)

(* NOTE: exists has been replaced with the equivalent built-in SML function List.exists. *)

(* TODO: partition *)

(* TODO: filter *)

(* NOTE: length has been replaced with the equivalent built-in SML function List.length. *)

(* TODO: last *)

(* TODO: butlast *)

(* TODO: find *)

(* TODO: el *)

(* NOTE: map has been replaced with the equivalent built-in SML function List.map. *)

(* TODO: allpairs *)

(* TODO: distinctpairs *)

fun chop_list n l =
  if n = 0 then ([],l) else
  let val (m,l') = chop_list (n-1) (tl l) in ((hd l)::m,l') end
  handle Fail _ => raise Fail "chop_list";;

(* TODO: replicate *)

(* TODO: insertat *)

(* TODO: forall2 *)
  
fun index x =
  let fun ind n l =
    case l of
      [] => raise Fail "index"
    | (h::t) => if x = h then n else ind (n + 1) t 
  in 
    ind 0
  end;;
  
fun unzip l =
  case l of
    [] => ([],[])
  | (x,y)::t =>
      let val (xs,ys) = unzip t in (x::xs,y::ys) end;;
      
(* ------------------------------------------------------------------------- *)
(* Whether the first of two items comes earlier in the list.                 *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Application of (presumably imperative) function over a list.              *)
(* ------------------------------------------------------------------------- *)

(* NOTE: do_list has been replaced with the built-in SML function List.app. *)

(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

fun assoc a l =
  case l of
    (x,y)::t => if x = a then y else assoc a t
  | [] => raise Fail "find";;
  
(* TODO: rev_assoc *)
  
(* ------------------------------------------------------------------------- *)
(* Merging of sorted lists (maintaining repetitions).                        *)
(* ------------------------------------------------------------------------- *)

fun merge ord l1 l2 =
  case l1 of
    [] => l2
  | h1::t1 => case l2 of
                [] => l1
              | h2::t2 => if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

(* ------------------------------------------------------------------------- *)
(* Bottom-up mergesort.                                                      *)
(* ------------------------------------------------------------------------- *)

fun sort ord =
  let fun mergepairs l1 l2 =
    case (l1,l2) of
        ([s],[]) => s
      | (l,[]) => mergepairs [] l
      | (l,[s1]) => mergepairs (s1::l) []
      | (l,(s1::s2::ss)) => mergepairs ((merge ord s1 s2)::l) ss in
  fn l => if l = [] then [] else mergepairs [] (List.map (fn x => [x]) l)
  end;;
  
(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

fun increasing f x y = (f x) < (f y);;

fun decreasing f x y = (f x) > (f y) ;;

(* ------------------------------------------------------------------------- *)
(* Eliminate repetitions of adjacent elements, with and without counting.    *)
(* ------------------------------------------------------------------------- *)

(* Like the F# version, = is used instead of the shallow comparison (== in ocaml) *)
fun uniq l =
    case l of
      x :: (t as y :: ys ) => 
        let val t' = uniq t in
            if x = y then t' 
            else
                x :: t'
        end
    | _ => l;;

(* TODO: repetitions *)

fun tryfind f l =
  case l of
      [] => raise Fail "tryfind"
    | (h::t) => 
      ((f h) handle Fail _ => tryfind f t);;

(* TODO: mapfilter *)

(* ------------------------------------------------------------------------- *)
(* Find list member that maximizes or minimizes a function.                  *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Set operations on ordered lists.                                          *)
(* ------------------------------------------------------------------------- *)

(* In OCaml and F# the comparison is build in to the language. It is not in SML, so many of the following functions also take an ordering function as input *)
fun setify ord l=
  let fun canonical lis =
     case lis of
       x::(rest as y::_) => ord x y < 0 andalso canonical rest
     | _ => true in
  if canonical l then l
  else uniq (sort (fn x => fn y => ord x y <= 0) l)
  end;;
     
fun union ord s1 s2=
  let fun union l1 l2 =
    case (l1,l2) of
        ([],l2) => l2
      | (l1,[]) => l1
      | ((l1 as h1::t1),(l2 as h2::t2)) =>
          if h1 = h2 then h1::(union t1 t2)
          else if ord h1 h2 = ~1 then h1::(union t1 l2)
          else h2::(union l1 t2) in
  union (setify ord s1) (setify ord s2)
  end;;

 fun union_str s1 s2 = union str_ord s1 s2;;
 fun union_sip p1 p2 = union sip_ord p1 p2;;
 
 (* TODO: intersect *)
 
fun subtract ord s1 s2=
  let fun subtract l1 l2 =
    case (l1,l2) of
        ([],l2) => []
      | (l1,[]) => l1
      | ((l1 as h1::t1),(l2 as h2::t2)) =>
          if h1 = h2 then subtract t1 t2
          else if ord h1 h2 = ~1 then h1::(subtract t1 l2)
          else subtract l1 t2 in
  subtract (setify ord s1) (setify ord s2)
  end;;
  
fun subtract_str s1 s2 = subtract str_ord s1 s2;;

(* TODO: subset, psubset *)

(* TODO: seteq *)

fun insert ord x s = union ord [x] s;;

fun insert_str x s = insert str_ord x s;;

(* TODO: image *)

(* ------------------------------------------------------------------------- *)
(* Union of a family of sets.                                                *)
(* ------------------------------------------------------------------------- *)

fun unions ord s = 
   let fun concat a b = a @ b in
   setify ord (itlist concat s [])
   end;;

fun unions_str s = unions str_ord s;;

(* ------------------------------------------------------------------------- *)
(* List membership. This does *not* assume the list is a set.                *)
(* ------------------------------------------------------------------------- *)

fun mem x lis =
    case lis of
      [] => false
    | hd :: tl => hd = x orelse mem x tl;;

    
(* ------------------------------------------------------------------------- *)
(* Finding all subsets or all subsets of a given size.                       *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Explosion and implosion of strings.                                       *)
(* ------------------------------------------------------------------------- *)

(* NOTE: explode has been replaced with the equivalent built-in SML function String.explode. *)

(* TODO: implode *)

(* ------------------------------------------------------------------------- *)
(* Timing; useful for documentation but not logically necessary.             *)
(* ------------------------------------------------------------------------- *)
  
fun time f x = 
    let val timer = Timer.startRealTimer()
        val result = f x
        val time = Timer.checkRealTimer timer
    in (
    print_string ("CPU time (user): " ^ (Real.toString (Time.toReal time)));
    print_newline();
    result
    ) end;;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;
 
(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

val undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

fun is_undefined f =
  case f of
    Empty => true
  | _ => false;;
  
(* ------------------------------------------------------------------------- *)
(* Operation analogous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

local 
  fun map_list f l =
        case l of
          [] => []
        | (x,y)::t => (x,f(y))::(map_list f t) 
in
  fun mapf f t =
        case t of
          Empty => Empty
        | Leaf(h,l) => Leaf(h,map_list f l)
        | Branch(p,b,l,r) => Branch(p,b,mapf f l,mapf f r) 
end;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)
  
(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

(* TODO *)
  
(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

(* There is no build-in polymorphic hash in SML, so a hash function must be passed in as a function *)
fun applyd ord hash f d x=
  let fun apply_listd l d x =
        case l of
          (a,b)::t => if x = a then b else if ord x a > 0 then apply_listd t d x else d x
        | [] => d x
      val k = hash x 
      fun look t =
        case t of
          Leaf(h,l) => 
            if (h = k) then 
              apply_listd l d x
            else d x
        | Branch(p,b,l,r) => 
            if ((k lxor p) land (b - 1)) = 0 then
              look (if k land b = 0 then l else r)
            else d x
        | _ => d x 
  in
  look f
  end
;;

fun apply ord hash f = applyd ord hash f (fn x => raise Fail "apply");;

fun apply_str f = apply str_ord str_hash f;;

fun tryapplyd ord hash f a d = applyd ord hash f (fn x => d) a;;

fun tryapplyd_str f a d = tryapplyd str_ord str_hash f a d;;

fun tryapplyl ord hash f x = tryapplyd ord hash f x [];;

fun defined ord hash f x = (apply ord hash f x; true) handle Fail _ => false;;

fun defined_str f x = defined str_ord str_hash f x;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

local
  fun undefine_list ord x l =
    case l of
      (ab as (a,b))::t =>
          let val c = ord x a in
          if c = 0 then 
            t
          else if c < 0 then 
            l
          else
            let val t' = undefine_list ord x t in
            ab::t' (* Like the F# version, = is used instead of the shallow comparison (== in ocaml) *)
            end
          end
    | [] => []
in
  fun undefine ord hash x =
    let val k = hash x 
        fun und t =
          case t of
            Leaf(h,l) =>
              if h=k then (
                let val l' = undefine_list ord x l in
                if l' = l then t (* Like the F# version, = is used instead of the shallow comparison (== in ocaml) *)
                else if l' = [] then Empty
                else Leaf(h,l')
                end
              ) else t
          | Branch(p,b,l,r) =>
              if k land (b - 1) = p then (
                if k land b = 0 then
                  let val l' = und l in
                  if l' = l then t (* Like the F# version, = is used instead of the shallow comparison (== in ocaml) *)
                  else (case l' of Empty => r | _ => Branch(p,b,l',r))
                  end
                else
                  let val r' = und r in
                  if r' = r then t (* Like the F# version, = is used instead of the shallow comparison (== in ocaml) *)
                  else (case r' of Empty => l | _ => Branch(p,b,l,r'))
                  end
              ) else t
          | _ => t 
    in
    und
    end
end;;

fun undefine_str x t = undefine str_ord str_hash x t

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

infix 6 |->

local
  fun newbranch p1 t1 p2 t2 =
        let val zp = p1 lxor p2 
            val b = zp land (~zp) 
            val p = p1 land (b - 1) in
        if p1 land b = 0 then Branch(p,b,t1,t2)
        else Branch(p,b,t2,t1)
        end 
  fun define_list ord (xy as (x,y)) l =
        case l of
          (ab as (a,b))::t =>
              let val c = ord x a in
              if c = 0 then xy::t
              else if c < 0 then xy::l
              else ab::(define_list ord xy t)
              end
        | [] => [xy]
  fun combine_list ord op' z l1 l2 =
        case (l1,l2) of
          ([],_) => l2
        | (_,[]) => l1
        | ((xy1 as (x1,y1))::t1,(xy2 as (x2,y2))::t2) =>
              let val c = ord x1 x2 in
              if c < 0 then 
                xy1::(combine_list ord op' z t1 l2)
              else if c > 0 then 
                xy2::(combine_list ord op' z l1 t2) 
              else
                let val y = op' y1 y2 
                    val l = combine_list ord op' z t1 t2 in
                if z(y) then l else (x1,y)::l
                end
              end
  in
  fun (x |-> y) t ord hash =
        let val k = hash x 
            fun upd t =
              case t of
                Empty => Leaf (k,[(x,y)])
              | Leaf(h,l) =>
                   if h = k then Leaf(h,define_list ord (x,y) l)
                   else newbranch h t k (Leaf(k,[(x,y)]))
              | Branch(p,b,l,r) =>
                  if k land (b - 1) <> p then newbranch p t k (Leaf(k,[(x,y)]))
                  else if k land b = 0 then Branch(p,b,upd l,r)
                  else Branch(p,b,l,upd r) in
        upd t
        end
  fun combine ord op' z t1 t2 =
        case (t1,t2) of
          (Empty,_) => t2
        | (_,Empty) => t1
        | (Leaf(h1,l1),Leaf(h2,l2)) =>
              if h1 = h2 then
                let val l = combine_list ord op' z l1 l2 in
                if l = [] then Empty else Leaf(h1,l)
                end
              else newbranch h1 t1 h2 t2
        | ((lf as Leaf(k,lis)),(br as Branch(p,b,l,r))) =>
              if k land (b - 1) = p then
                if k land b = 0 then
                  (case combine ord op' z lf l of
                     Empty => r | l' => Branch(p,b,l',r))
                else
                  (case combine ord op' z lf r of
                     Empty => l | r' => Branch(p,b,l,r'))
              else
                newbranch k lf p br
        | ((br as Branch(p,b,l,r)),(lf as Leaf(k,lis))) =>
              if k land (b - 1) = p then
                if k land b = 0 then
                  (case combine ord op' z l lf of
                    Empty => r | l' => Branch(p,b,l',r))
                else
                  (case combine ord op' z r lf of
                     Empty => l | r' => Branch(p,b,l,r'))
              else
                newbranch p br k lf
        | (Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2)) =>
              if b1 < b2 then
                if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
                else if p2 land b1 = 0 then
                  (case combine ord op' z l1 t2 of
                     Empty => r1 | l => Branch(p1,b1,l,r1))
                else
                  (case combine ord op' z r1 t2 of
                     Empty => l1 | r => Branch(p1,b1,l1,r))
              else if b2 < b1 then
                if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
                else if p1 land b2 = 0 then
                  (case combine ord op' z t1 l2 of
                     Empty => r2 | l => Branch(p2,b2,l,r2))
                else
                  (case combine ord op' z t1 r2 of
                     Empty => l2 | r => Branch(p2,b2,l2,r))
              else if p1 = p2 then
               (case (combine ord op' z l1 l2,combine ord op' z r1 r2) of
                  (Empty,r) => r | (l,Empty) => l | (l,r) => Branch(p1,b1,l,r))
              else
                newbranch p1 t1 p2 t2 
end ;;

infix 6 |--> (* For strings *)

fun (x |--> y) t = (x |-> y) t str_ord str_hash;;

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

infix 6 |=>

fun x |=> y = (x |-> y) undefined;;

infix 6 |==> (* For strings *)

fun x |==> y = (x |=> y) str_ord str_hash;;

(* ------------------------------------------------------------------------- *)
(* Idiom for a mapping zipping domain and range lists.                       *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Install a (trivial) printer for finite partial functions.                 *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Related stuff for standard functions.                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* Union-find algorithm.                                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO *)

(* ------------------------------------------------------------------------- *)
(* First number starting at n for which p succeeds.                          *)
(* ------------------------------------------------------------------------- *)

(* TODO *)
