open Num;;
open Format;;
(* ========================================================================= *)
(* Tweak OCaml default state ready for theorem proving code.                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };; (* Up the stack size  *)
Format.set_margin 72;;                                 (* Reduce margins     *)
include Format;;                                       (* Open formatting    *)
include Num;;                                          (* Open bignums       *)

let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)
(*
#install_printer print_num;;                           (* when printing nums *)
*)
(* ========================================================================= *)
(* Misc library functions to set up a nice environment.                      *)
(* ========================================================================= *)

let identity x = x;;

let ( ** ) = fun f g x -> f(g x);;

(* ------------------------------------------------------------------------- *)
(* GCD and LCM on arbitrary-precision numbers.                               *)
(* ------------------------------------------------------------------------- *)

let gcd_num n1 n2 =
  abs_num(num_of_big_int
      (Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2)));;

let lcm_num n1 n2 = abs_num(n1 */ n2) // gcd_num n1 n2;;

(* ------------------------------------------------------------------------- *)
(* A useful idiom for "non contradictory" etc.                               *)
(* ------------------------------------------------------------------------- *)

let non p x = not(p x);;

(* ------------------------------------------------------------------------- *)
(* Kind of assertion checking.                                               *)
(* ------------------------------------------------------------------------- *)

let check p x = if p(x) then x else failwith "check";;

(* ------------------------------------------------------------------------- *)
(* Repetition of a function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let can f x = try f x; true with Failure _ -> false;;

let rec repeat f x = try repeat f (f x) with Failure _ -> x;;

(* ------------------------------------------------------------------------- *)
(* Handy list operations.                                                    *)
(* ------------------------------------------------------------------------- *)

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;

let rec (---) = fun m n -> if m >/ n then [] else m::((m +/ Int 1) --- n);;

let rec map2 f l1 l2 =
  match (l1,l2) with
    [],[] -> []
  | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
  | _ -> failwith "map2: length mismatch";;

let rev =
  let rec rev_append acc l =
    match l with
      [] -> acc
    | h::t -> rev_append (h::acc) t in
  fun l -> rev_append [] l;;

let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) & forall p t;;

let rec exists p l =
  match l with
    [] -> false
  | h::t -> p(h) or exists p t;;

let partition p l =
    itlist (fun a (yes,no) -> if p a then a::yes,no else yes,a::no) l ([],[]);;

let filter p l = fst(partition p l);;

let length =
  let rec len k l =
    if l = [] then k else len (k + 1) (tl l) in
  fun l -> len 0 l;;

let rec last l =
  match l with
    [x] -> x
  | (h::t) -> last t
  | [] -> failwith "last";;

let rec butlast l =
  match l with
    [_] -> []
  | (h::t) -> h::(butlast t)
  | [] -> failwith "butlast";;

let rec find p l =
  match l with
      [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t;;

let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;

let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;

let rec chop_list n l =
  if n = 0 then [],l else
  try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
  with Failure _ -> failwith "chop_list";;

let replicate n a = map (fun x -> a) (1--n);;

let rec insertat i x l =
  if i = 0 then x::l else
  match l with
    [] -> failwith "insertat: list too short for position to exist"
  | h::t -> h::(insertat (i-1) x t);;

let rec forall2 p l1 l2 =
  match (l1,l2) with
    [],[] -> true
  | (h1::t1,h2::t2) -> p h1 h2 & forall2 p t1 t2
  | _ -> false;;

let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
  ind 0;;

let rec unzip l =
  match l with
    [] -> [],[]
  | (x,y)::t ->
      let xs,ys = unzip t in x::xs,y::ys;;

(* ------------------------------------------------------------------------- *)
(* Whether the first of two items comes earlier in the list.                 *)
(* ------------------------------------------------------------------------- *)

let rec earlier l x y =
  match l with
    h::t -> (Pervasives.compare h y <> 0) &
            (Pervasives.compare h x = 0 or earlier t x y)
  | [] -> false;;

(* ------------------------------------------------------------------------- *)
(* Application of (presumably imperative) function over a list.              *)
(* ------------------------------------------------------------------------- *)

let rec do_list f l =
  match l with
    [] -> ()
  | h::t -> f(h); do_list f t;;

(* ------------------------------------------------------------------------- *)
(* Association lists.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare x a = 0 then y else assoc a t
  | [] -> failwith "find";;

let rec rev_assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assoc a t
  | [] -> failwith "find";;

(* ------------------------------------------------------------------------- *)
(* Merging of sorted lists (maintaining repetitions).                        *)
(* ------------------------------------------------------------------------- *)

let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

(* ------------------------------------------------------------------------- *)
(* Bottom-up mergesort.                                                      *)
(* ------------------------------------------------------------------------- *)

let sort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;

(* ------------------------------------------------------------------------- *)
(* Common measure predicates to use with "sort".                             *)
(* ------------------------------------------------------------------------- *)

let increasing f x y = Pervasives.compare (f x) (f y) < 0;;

let decreasing f x y = Pervasives.compare (f x) (f y) > 0;;

(* ------------------------------------------------------------------------- *)
(* Eliminate repetitions of adjacent elements, with and without counting.    *)
(* ------------------------------------------------------------------------- *)

let rec uniq l =
  match l with
    x::(y::_ as t) -> let t' = uniq t in
                      if Pervasives.compare x y = 0 then t' else
                      if t'==t then l else x::t'
 | _ -> l;;

let repetitions =
  let rec repcount n l =
    match l with
      x::(y::_ as ys) -> if Pervasives.compare y x = 0 then repcount (n + 1) ys
                  else (x,n)::(repcount 1 ys)
    | [x] -> [x,n]
    | [] -> failwith "repcount" in
  fun l -> if l = [] then [] else repcount 1 l;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest;;

(* ------------------------------------------------------------------------- *)
(* Find list member that maximizes or minimizes a function.                  *)
(* ------------------------------------------------------------------------- *)

let optimize ord f l =
  fst(end_itlist (fun (x,y as p) (x',y' as p') -> if ord y y' then p else p')
                 (map (fun x -> x,f x) l));;

let maximize f l = optimize (>) f l and minimize f l = optimize (<) f l;;

(* ------------------------------------------------------------------------- *)
(* Set operations on ordered lists.                                          *)
(* ------------------------------------------------------------------------- *)

let setify =
  let rec canonical lis =
     match lis with
       x::(y::_ as rest) -> Pervasives.compare x y < 0 & canonical rest
     | _ -> true in
  fun l -> if canonical l then l
           else uniq (sort (fun x y -> Pervasives.compare x y <= 0) l);;

let union =
  let rec union l1 l2 =
    match (l1,l2) with
        ([],l2) -> l2
      | (l1,[]) -> l1
      | ((h1::t1 as l1),(h2::t2 as l2)) ->
          if h1 = h2 then h1::(union t1 t2)
          else if h1 < h2 then h1::(union t1 l2)
          else h2::(union l1 t2) in
  fun s1 s2 -> union (setify s1) (setify s2);;

let intersect =
  let rec intersect l1 l2 =
    match (l1,l2) with
        ([],l2) -> []
      | (l1,[]) -> []
      | ((h1::t1 as l1),(h2::t2 as l2)) ->
          if h1 = h2 then h1::(intersect t1 t2)
          else if h1 < h2 then intersect t1 l2
          else intersect l1 t2 in
  fun s1 s2 -> intersect (setify s1) (setify s2);;

let subtract =
  let rec subtract l1 l2 =
    match (l1,l2) with
        ([],l2) -> []
      | (l1,[]) -> l1
      | ((h1::t1 as l1),(h2::t2 as l2)) ->
          if h1 = h2 then subtract t1 t2
          else if h1 < h2 then h1::(subtract t1 l2)
          else subtract l1 t2 in
  fun s1 s2 -> subtract (setify s1) (setify s2);;

let subset,psubset =
  let rec subset l1 l2 =
    match (l1,l2) with
        ([],l2) -> true
      | (l1,[]) -> false
      | (h1::t1,h2::t2) ->
          if h1 = h2 then subset t1 t2
          else if h1 < h2 then false
          else subset l1 t2
  and psubset l1 l2 =
    match (l1,l2) with
        (l1,[]) -> false
      | ([],l2) -> true
      | (h1::t1,h2::t2) ->
          if h1 = h2 then psubset t1 t2
          else if h1 < h2 then false
          else subset l1 t2 in
  (fun s1 s2 -> subset (setify s1) (setify s2)),
  (fun s1 s2 -> psubset (setify s1) (setify s2));;

let rec set_eq s1 s2 = (setify s1 = setify s2);;

let insert x s = union [x] s;;

let image f s = setify (map f s);;

(* ------------------------------------------------------------------------- *)
(* Union of a family of sets.                                                *)
(* ------------------------------------------------------------------------- *)

let unions s = setify(itlist (@) s []);;

(* ------------------------------------------------------------------------- *)
(* List membership. This does *not* assume the list is a set.                *)
(* ------------------------------------------------------------------------- *)

let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 or mem x t;;

(* ------------------------------------------------------------------------- *)
(* Finding all subsets or all subsets of a given size.                       *)
(* ------------------------------------------------------------------------- *)

let rec allsets m l =
  if m = 0 then [[]] else
  match l with
    [] -> []
  | h::t -> union (image (fun g -> h::g) (allsets (m - 1) t)) (allsets m t);;

let rec allsubsets s =
  match s with
    [] -> [[]]
  | (a::t) -> let res = allsubsets t in
              union (image (fun b -> a::b) res) res;;

let allnonemptysubsets s = subtract (allsubsets s) [[]];;

(* ------------------------------------------------------------------------- *)
(* Explosion and implosion of strings.                                       *)
(* ------------------------------------------------------------------------- *)

let explode s =
  let rec exap n l =
     if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;

let implode l = itlist (^) l "";;

(* ------------------------------------------------------------------------- *)
(* Timing; useful for documentation but not logically necessary.             *)
(* ------------------------------------------------------------------------- *)

let time f x =
  let start_time = Sys.time() in
  let result = f x in
  let finish_time = Sys.time() in
  print_string
    ("CPU time (user): "^(string_of_float(finish_time -. start_time)));
  print_newline();
  result;;

(* ------------------------------------------------------------------------- *)
(* Polymorphic finite partial functions via Patricia trees.                  *)
(*                                                                           *)
(* The point of this strange representation is that it is canonical (equal   *)
(* functions have the same encoding) yet reasonably efficient on average.    *)
(*                                                                           *)
(* Idea due to Diego Olivier Fernandez Pons (OCaml list, 2003/11/10).        *)
(* ------------------------------------------------------------------------- *)

type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;

(* ------------------------------------------------------------------------- *)
(* Undefined function.                                                       *)
(* ------------------------------------------------------------------------- *)

let undefined = Empty;;

(* ------------------------------------------------------------------------- *)
(* In case of equality comparison worries, better use this.                  *)
(* ------------------------------------------------------------------------- *)

let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Operation analogous to "map" for lists.                                   *)
(* ------------------------------------------------------------------------- *)

let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;

(* ------------------------------------------------------------------------- *)
(* Operations analogous to "fold" for lists.                                 *)
(* ------------------------------------------------------------------------- *)

let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;

(* ------------------------------------------------------------------------- *)
(* Mapping to sorted-list representation of the graph, domain and range.     *)
(* ------------------------------------------------------------------------- *)

let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

let ran f = setify(foldl (fun a x y -> y::a) [] f);;

(* ------------------------------------------------------------------------- *)
(* Application.                                                              *)
(* ------------------------------------------------------------------------- *)

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> let c = Pervasives.compare x a in
                  if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
                -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let tryapplyl f x = tryapplyd f x [];;

let defined f x = try apply f x; true with Failure _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Undefinition.                                                             *)
(* ------------------------------------------------------------------------- *)

let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then t
          else if c < 0 then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else (match l' with Empty -> r | _ -> Branch(p,b,l',r))
          else
            let r' = und r in
            if r' == r then t
            else (match r' with Empty -> l | _ -> Branch(p,b,l,r'))
      | _ -> t in
    und;;

(* ------------------------------------------------------------------------- *)
(* Redefinition and combination.                                             *)
(* ------------------------------------------------------------------------- *)

let (|->),combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then xy::t
          else if c < 0 then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          let c = Pervasives.compare x1 x2 in
          if c < 0 then xy1::(combine_list op z t1 l2)
          else if c > 0 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z lf l with
                 Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z lf r with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch k lf p br
    | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z l lf with
                Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z r lf with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch p br k lf
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              (match combine op z l1 t2 with
                 Empty -> r1 | l -> Branch(p1,b1,l,r1))
            else
              (match combine op z r1 t2 with
                 Empty -> l1 | r -> Branch(p1,b1,l1,r))
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              (match combine op z t1 l2 with
                 Empty -> r2 | l -> Branch(p2,b2,l,r2))
            else
              (match combine op z t1 r2 with
                 Empty -> l2 | r -> Branch(p2,b2,l2,r))
          else if p1 = p2 then
           (match (combine op z l1 l2,combine op z r1 r2) with
              (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;

(* ------------------------------------------------------------------------- *)
(* Special case of point function.                                           *)
(* ------------------------------------------------------------------------- *)

let (|=>) = fun x y -> (x |-> y) undefined;;

(* ------------------------------------------------------------------------- *)
(* Idiom for a mapping zipping domain and range lists.                       *)
(* ------------------------------------------------------------------------- *)

let fpf xs ys = itlist2 (|->) xs ys undefined;;

(* ------------------------------------------------------------------------- *)
(* Grab an arbitrary element.                                                *)
(* ------------------------------------------------------------------------- *)

let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> hd l
  | Branch(b,p,t1,t2) -> choose t1;;

(* ------------------------------------------------------------------------- *)
(* Install a (trivial) printer for finite partial functions.                 *)
(* ------------------------------------------------------------------------- *)

let print_fpf (f:('a,'b)func) = print_string "<func>";;

#install_printer print_fpf;;

(* ------------------------------------------------------------------------- *)
(* Related stuff for standard functions.                                     *)
(* ------------------------------------------------------------------------- *)

let valmod a y f x = if x = a then y else f(x);;

let undef x = failwith "undefined function";;

(* ------------------------------------------------------------------------- *)
(* Union-find algorithm.                                                     *)
(* ------------------------------------------------------------------------- *)

type ('a)pnode = Nonterminal of 'a | Terminal of 'a * int;;

type ('a)partition = Partition of ('a,('a)pnode)func;;

let rec terminus (Partition f as ptn) a =
  match (apply f a) with
    Nonterminal(b) -> terminus ptn b
  | Terminal(p,q) -> (p,q);;

let tryterminus ptn a =
  try terminus ptn a with Failure _ -> (a,1);;

let canonize ptn a = fst(tryterminus ptn a);;

let equivalent eqv a b = canonize eqv a = canonize eqv b;;

let equate (a,b) (Partition f as ptn) =
  let (a',na) = tryterminus ptn a
  and (b',nb) = tryterminus ptn b in
  Partition
   (if a' = b' then f else
    if na <= nb then
       itlist identity [a' |-> Nonterminal b'; b' |-> Terminal(b',na+nb)] f
    else
       itlist identity [b' |-> Nonterminal a'; a' |-> Terminal(a',na+nb)] f);;

let unequal = Partition undefined;;

let equated (Partition f) = dom f;;

(* ------------------------------------------------------------------------- *)
(* First number starting at n for which p succeeds.                          *)
(* ------------------------------------------------------------------------- *)

let rec first n p = if p(n) then n else first (n +/ Int 1) p;;
(* ========================================================================= *)
(* Simple algebraic expression example from the introductory chapter.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type expression =
   Var of string
 | Const of int
 | Add of expression * expression
 | Mul of expression * expression;;

(* ------------------------------------------------------------------------- *)
(* Trivial example of using the type constructors.                           *)
(* ------------------------------------------------------------------------- *)

(*
Add(Mul(Const 2,Var "x"),Var "y");;
*)

(* ------------------------------------------------------------------------- *)
(* Simplification example.                                                   *)
(* ------------------------------------------------------------------------- *)

let simplify1 expr =
  match expr with
    Add(Const(m),Const(n)) -> Const(m + n)
  | Mul(Const(m),Const(n)) -> Const(m * n)
  | Add(Const(0),x) -> x
  | Add(x,Const(0)) -> x
  | Mul(Const(0),x) -> Const(0)
  | Mul(x,Const(0)) -> Const(0)
  | Mul(Const(1),x) -> x
  | Mul(x,Const(1)) -> x
  | _ -> expr;;

let rec simplify expr =
  match expr with
    Add(e1,e2) -> simplify1(Add(simplify e1,simplify e2))
  | Mul(e1,e2) -> simplify1(Mul(simplify e1,simplify e2))
  | _ -> simplify1 expr;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)
(*
let e = Add(Mul(Add(Mul(Const(0),Var "x"),Const(1)),Const(3)),
            Const(12));;
simplify e;;
*)

(* ------------------------------------------------------------------------- *)
(* Lexical analysis.                                                         *)
(* ------------------------------------------------------------------------- *)

let matches s = let chars = explode s in fun c -> mem c chars;;

let space = matches " \t\n\r"
and punctuation = matches "()[]{},"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"
and alphanumeric = matches
  "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";;

let rec lexwhile prop inp =
  match inp with
    c::cs when prop c -> let tok,rest = lexwhile prop cs in c^tok,rest
  | _ -> "",inp;;

let rec lex inp =
  match snd(lexwhile space inp) with
    [] -> []
  | c::cs -> let prop = if alphanumeric(c) then alphanumeric
                        else if symbolic(c) then symbolic
                        else fun c -> false in
             let toktl,rest = lexwhile prop cs in
             (c^toktl)::lex rest;;

(*
lex(explode "2*((var_1 + x') + 11)");;
lex(explode "if (*p1-- == *p2++) then f() else g()");;
*)

(* ------------------------------------------------------------------------- *)
(* Parsing.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec parse_expression i =
  match parse_product i with
    e1,"+"::i1 -> let e2,i2 = parse_expression i1 in Add(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_product i =
  match parse_atom i with
    e1,"*"::i1 -> let e2,i2 = parse_product i1 in Mul(e1,e2),i2
  | e1,i1 -> e1,i1

and parse_atom i =
  match i with
    [] -> failwith "Expected an expression at end of input"
  | "("::i1 -> (match parse_expression i1 with
                  e2,")"::i2 -> e2,i2
                | _ -> failwith "Expected closing bracket")
  | tok::i1 -> if forall numeric (explode tok)
               then Const(int_of_string tok),i1
               else Var(tok),i1;;

(* ------------------------------------------------------------------------- *)
(* Generic function to impose lexing and exhaustion checking on a parser.    *)
(* ------------------------------------------------------------------------- *)

let make_parser pfn s =
  let expr,rest = pfn (lex(explode s)) in
  if rest = [] then expr else failwith "Unparsed input";;

(* ------------------------------------------------------------------------- *)
(* Our parser.                                                               *)
(* ------------------------------------------------------------------------- *)

let default_parser = make_parser parse_expression;;

(*
default_parser "x + 1";;

(* ------------------------------------------------------------------------- *)
(* Demonstrate automatic installation.                                       *)
(* ------------------------------------------------------------------------- *)

<<(x1 + x2 + x3) * (1 + 2 + 3 * x + y)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Conservatively bracketing first attempt at printer.                       *)
(* ------------------------------------------------------------------------- *)

let rec string_of_exp e =
  match e with
    Var s -> s
  | Const n -> string_of_int n
  | Add(e1,e2) -> "("^(string_of_exp e1)^" + "^(string_of_exp e2)^")"
  | Mul(e1,e2) -> "("^(string_of_exp e1)^" * "^(string_of_exp e2)^")";;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
string_of_exp <<x + 3 * y>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Somewhat better attempt.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec string_of_exp pr e =
  match e with
    Var s -> s
  | Const n -> string_of_int n
  | Add(e1,e2) ->
        let s = (string_of_exp 3 e1)^" + "^(string_of_exp 2 e2) in
        if 2 < pr then "("^s^")" else s
  | Mul(e1,e2) ->
        let s = (string_of_exp 5 e1)^" * "^(string_of_exp 4 e2) in
        if 4 < pr then "("^s^")" else s;;

(* ------------------------------------------------------------------------- *)
(* Install it.                                                               *)
(* ------------------------------------------------------------------------- *)

let print_exp e = Format.print_string ("<<"^string_of_exp 0 e^">>");;

#install_printer print_exp;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
<<x + 3 * y>>;;
<<(x + 3) * y>>;;
<<1 + 2 + 3>>;;
<<((1 + 2) + 3) + 4>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Example shows the problem.                                                *)
(* ------------------------------------------------------------------------- *)

(*
<<(x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10) *
  (y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 + y9 + y10)>>;;
*)
(* ========================================================================= *)
(* Polymorphic type of formulas with parser and printer.                     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type ('a)formula = False
                 | True
                 | Atom of 'a
                 | Not of ('a)formula
                 | And of ('a)formula * ('a)formula
                 | Or of ('a)formula * ('a)formula
                 | Imp of ('a)formula * ('a)formula
                 | Iff of ('a)formula * ('a)formula
                 | Forall of string * ('a)formula
                 | Exists of string * ('a)formula;;

(* ------------------------------------------------------------------------- *)
(* General parsing of iterated infixes.                                      *)
(* ------------------------------------------------------------------------- *)

let rec parse_ginfix opsym opupdate sof subparser inp =
  let e1,inp1 = subparser inp in
  if inp1 <> [] & hd inp1 = opsym then
     parse_ginfix opsym opupdate (opupdate sof e1) subparser (tl inp1)
  else sof e1,inp1;;

let parse_left_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> opcon(f e1,e2)) (fun x -> x);;

let parse_right_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> f(opcon(e1,e2))) (fun x -> x);;

let parse_list opsym =
  parse_ginfix opsym (fun f e1 e2 -> (f e1)@[e2]) (fun x -> [x]);;

(* ------------------------------------------------------------------------- *)
(* Other general parsing combinators.                                        *)
(* ------------------------------------------------------------------------- *)

let papply f (ast,rest) = (f ast,rest);;

let nextin inp tok = inp <> [] & hd inp = tok;;

let parse_bracketed subparser cbra inp =
  let ast,rest = subparser inp in
  if nextin rest cbra then ast,tl rest
  else failwith "Closing bracket expected";;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas, parametrized by atom parser "pfn".                   *)
(* ------------------------------------------------------------------------- *)

let rec parse_atomic_formula (ifn,afn) vs inp =
  match inp with
    [] -> failwith "formula expected"
  | "false"::rest -> False,rest
  | "true"::rest -> True,rest
  | "("::rest -> (try ifn vs inp with Failure _ ->
                  parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
  | "~"::rest -> papply (fun p -> Not p)
                        (parse_atomic_formula (ifn,afn) vs rest)
  | "forall"::x::rest ->
        parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest
  | "exists"::x::rest ->
        parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest
  | _ -> afn vs inp

and parse_quant (ifn,afn) vs qcon x inp =
   match inp with
     [] -> failwith "Body of quantified term expected"
   | y::rest ->
        papply (fun fm -> qcon(x,fm))
               (if y = "." then parse_formula (ifn,afn) vs rest
                else parse_quant (ifn,afn) (y::vs) qcon y rest)

and parse_formula (ifn,afn) vs inp =
   parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
     (parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
         (parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
             (parse_right_infix "/\\" (fun (p,q) -> And(p,q))
                  (parse_atomic_formula (ifn,afn) vs)))) inp;;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas, parametrized by atom printer.                       *)
(* ------------------------------------------------------------------------- *)

let bracket p n f x y =
  (if p then print_string "(" else ());
  open_box n; f x y; close_box();
  (if p then print_string ")" else ());;

let rec strip_quant fm =
  match fm with
    Forall(x,(Forall(y,p) as yp)) | Exists(x,(Exists(y,p) as yp)) ->
        let xs,q = strip_quant yp in x::xs,q
  |  Forall(x,p) | Exists(x,p) -> [x],p
  | _ -> [],fm;;

let print_formula pfn =
  let rec print_formula pr fm =
    match fm with
      False -> print_string "false"
    | True -> print_string "true"
    | Atom(pargs) -> pfn pr pargs
    | Not(p) -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And(p,q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or(p,q) ->  bracket (pr > 6) 0 (print_infix  6 "\\/") p q
    | Imp(p,q) ->  bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff(p,q) ->  bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall(x,p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists(x,p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
  and print_qnt qname (bvs,bod) =
    print_string qname;
    do_list (fun v -> print_string " "; print_string v) bvs;
    print_string "."; print_space(); open_box 0;
    print_formula 0 bod;
    close_box()
  and print_prefix newpr sym p =
   print_string sym; print_formula (newpr+1) p
  and print_infix newpr sym p q =
    print_formula (newpr+1) p;
    print_string(" "^sym); print_space();
    print_formula newpr q in
  print_formula 0;;

let print_qformula pfn fm =
  open_box 0; print_string "<<";
  open_box 0; print_formula pfn fm; close_box();
  print_string ">>"; close_box();;

(* ------------------------------------------------------------------------- *)
(* OCaml won't let us use the constructors.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_and p q = And(p,q) and mk_or p q = Or(p,q)
and mk_imp p q = Imp(p,q) and mk_iff p q = Iff(p,q)
and mk_forall x p = Forall(x,p) and mk_exists x p = Exists(x,p);;

(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

let dest_iff fm =
  match fm with Iff(p,q) -> (p,q) | _ -> failwith "dest_iff";;

let dest_and fm =
  match fm with And(p,q) -> (p,q) | _ -> failwith "dest_and";;

let rec conjuncts fm =
  match fm with And(p,q) -> conjuncts p @ conjuncts q | _ -> [fm];;

let dest_or fm =
  match fm with Or(p,q) -> (p,q) | _ -> failwith "dest_or";;

let rec disjuncts fm =
  match fm with Or(p,q) -> disjuncts p @ disjuncts q | _ -> [fm];;

let dest_imp fm =
  match fm with Imp(p,q) -> (p,q) | _ -> failwith "dest_imp";;

let antecedent fm = fst(dest_imp fm);;
let consequent fm = snd(dest_imp fm);;

(* ------------------------------------------------------------------------- *)
(* Apply a function to the atoms, otherwise keeping structure.               *)
(* ------------------------------------------------------------------------- *)

let rec onatoms f fm =
  match fm with
    Atom a -> f a
  | Not(p) -> Not(onatoms f p)
  | And(p,q) -> And(onatoms f p,onatoms f q)
  | Or(p,q) -> Or(onatoms f p,onatoms f q)
  | Imp(p,q) -> Imp(onatoms f p,onatoms f q)
  | Iff(p,q) -> Iff(onatoms f p,onatoms f q)
  | Forall(x,p) -> Forall(x,onatoms f p)
  | Exists(x,p) -> Exists(x,onatoms f p)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Formula analog of list iterator "itlist".                                 *)
(* ------------------------------------------------------------------------- *)

let rec overatoms f fm b =
  match fm with
    Atom(a) -> f a b
  | Not(p) -> overatoms f p b
  | And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q) ->
        overatoms f p (overatoms f q b)
  | Forall(x,p) | Exists(x,p) -> overatoms f p b
  | _ -> b;;

(* ------------------------------------------------------------------------- *)
(* Special case of a union of the results of a function over the atoms.      *)
(* ------------------------------------------------------------------------- *)

let atom_union f fm = setify (overatoms (fun h t -> f(h)@t) fm []);;
(* ========================================================================= *)
(* Basic stuff for propositional logic: datatype, parsing and printing.      *)
(* ========================================================================= *)

type prop = P of string;;

let pname(P s) = s;;

(* ------------------------------------------------------------------------- *)
(* Parsing of propositional formulas.                                        *)
(* ------------------------------------------------------------------------- *)

let parse_propvar vs inp =
  match inp with
    p::oinp when p <> "(" -> Atom(P(p)),oinp
  | _ -> failwith "parse_propvar";;

let parse_prop_formula = make_parser
  (parse_formula ((fun _ _ -> failwith ""),parse_propvar) []);;

(* ------------------------------------------------------------------------- *)
(* Set this up as default for quotations.                                    *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse_prop_formula;;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_propvar prec p = print_string(pname p);;

let print_prop_formula = print_qformula print_propvar;;

#install_printer print_prop_formula;;

(* ------------------------------------------------------------------------- *)
(* Testing the parser and printer.                                           *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<p ==> q <=> r /\ s \/ (t <=> ~ ~u /\ v)>>;;

And(fm,fm);;

And(Or(fm,fm),fm);;
*)

(* ------------------------------------------------------------------------- *)
(* Interpretation of formulas.                                               *)
(* ------------------------------------------------------------------------- *)

let rec eval fm v =
  match fm with
    False -> false
  | True -> true
  | Atom(x) -> v(x)
  | Not(p) -> not(eval p v)
  | And(p,q) -> (eval p v) & (eval q v)
  | Or(p,q) -> (eval p v) or (eval q v)
  | Imp(p,q) -> not(eval p v) or (eval q v)
  | Iff(p,q) -> (eval p v) = (eval q v);;

(* ------------------------------------------------------------------------- *)
(* Example of use.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
eval <<p /\ q ==> q /\ r>>
     (function P"p" -> true | P"q" -> false | P"r" -> true);;

eval <<p /\ q ==> q /\ r>>
     (function P"p" -> true | P"q" -> true | P"r" -> false);;
*)

(* ------------------------------------------------------------------------- *)
(* Return the set of propositional variables in a formula.                   *)
(* ------------------------------------------------------------------------- *)

let atoms fm = atom_union (fun a -> [a]) fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
atoms <<p /\ q \/ s ==> ~p \/ (r <=> s)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Code to print out truth tables.                                           *)
(* ------------------------------------------------------------------------- *)

let rec onallvaluations subfn v ats =
  match ats with
    [] -> subfn v
  | p::ps -> let v' t q = if q = p then t else v(q) in
             onallvaluations subfn (v' false) ps &
             onallvaluations subfn (v' true) ps;;

let print_truthtable fm =
  let ats = atoms fm in
  let width = itlist (max ** String.length ** pname) ats 5 + 1 in
  let fixw s = s^String.make(width - String.length s) ' ' in
  let truthstring p = fixw (if p then "true" else "false") in
  let mk_row v =
     let lis = map (fun x -> truthstring(v x)) ats
     and ans = truthstring(eval fm v) in
     print_string(itlist (^) lis ("| "^ans)); print_newline(); true in
  let separator = String.make (width * length ats + 9) '-' in
  print_string(itlist (fun s t -> fixw(pname s) ^ t) ats "| formula");
  print_newline(); print_string separator; print_newline();
  let _ = onallvaluations mk_row (fun x -> false) ats in
  print_string separator; print_newline();;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
print_truthtable <<p /\ q ==> q /\ r>>;;

let fm = <<p /\ q ==> q /\ r>>;;

print_truthtable fm;;
*)

(* ------------------------------------------------------------------------- *)
(* Additional examples illustrating formula classes.                         *)
(* ------------------------------------------------------------------------- *)

(*
print_truthtable <<((p ==> q) ==> p) ==> p>>;;

print_truthtable <<p /\ ~p>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Recognizing tautologies.                                                  *)
(* ------------------------------------------------------------------------- *)

let tautology fm =
  onallvaluations (eval fm) (fun s -> false) (atoms fm);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*

tautology <<p \/ ~p>>;;

tautology <<p \/ q ==> p>>;;

tautology <<p \/ q ==> q \/ (p <=> q)>>;;

tautology <<(p \/ q) /\ ~(p /\ q) ==> (~p <=> q)>>;;

*)

(* ------------------------------------------------------------------------- *)
(* Related concepts.                                                         *)
(* ------------------------------------------------------------------------- *)

let unsatisfiable fm = tautology(Not fm);;

let satisfiable fm = not(unsatisfiable fm);;

(* ------------------------------------------------------------------------- *)
(* Substitution operation.                                                   *)
(* ------------------------------------------------------------------------- *)

let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
psubst (P"p" |=> <<p /\ q>>) <<p /\ q /\ p /\ q>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Surprising tautologies including Dijkstra's "Golden rule".                *)
(* ------------------------------------------------------------------------- *)

(*
tautology <<(p ==> q) \/ (q ==> p)>>;;

tautology <<p \/ (q <=> r) <=> (p \/ q <=> p \/ r)>>;;

tautology <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

tautology <<(p ==> q) <=> (~q ==> ~p)>>;;

tautology <<(p ==> ~q) <=> (q ==> ~p)>>;;

tautology <<(p ==> q) <=> (q ==> p)>>;;

(* ------------------------------------------------------------------------- *)
(* Some logical equivalences allowing elimination of connectives.            *)
(* ------------------------------------------------------------------------- *)

forall tautology
 [<<true <=> false ==> false>>;
  <<~p <=> p ==> false>>;
  <<p /\ q <=> (p ==> q ==> false) ==> false>>;
  <<p \/ q <=> (p ==> false) ==> q>>;
  <<(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false>>];;
*)

(* ------------------------------------------------------------------------- *)
(* Dualization.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec dual fm =
  match fm with
    False -> True
  | True -> False
  | Atom(p) -> fm
  | Not(p) -> Not(dual p)
  | And(p,q) -> Or(dual p,dual q)
  | Or(p,q) -> And(dual p,dual q)
  | _ -> failwith "Formula involves connectives ==> or <=>";;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
dual <<p \/ ~p>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Routine simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let psimplify1 fm =
  match fm with
    Not False -> True
  | Not True -> False
  | Not(Not p) -> p
  | And(p,False) | And(False,p) -> False
  | And(p,True) | And(True,p) -> p
  | Or(p,False) | Or(False,p) -> p
  | Or(p,True) | Or(True,p) -> True
  | Imp(False,p) | Imp(p,True) -> True
  | Imp(True,p) -> p
  | Imp(p,False) -> Not p
  | Iff(p,True) | Iff(True,p) -> p
  | Iff(p,False) | Iff(False,p) -> Not p
  | _ -> fm;;

let rec psimplify fm =
  match fm with
  | Not p -> psimplify1 (Not(psimplify p))
  | And(p,q) -> psimplify1 (And(psimplify p,psimplify q))
  | Or(p,q) -> psimplify1 (Or(psimplify p,psimplify q))
  | Imp(p,q) -> psimplify1 (Imp(psimplify p,psimplify q))
  | Iff(p,q) -> psimplify1 (Iff(psimplify p,psimplify q))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
psimplify <<(true ==> (x <=> false)) ==> ~(y \/ false /\ z)>>;;

psimplify <<((x ==> y) ==> true) \/ ~false>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Some operations on literals.                                              *)
(* ------------------------------------------------------------------------- *)

let negative = function (Not p) -> true | _ -> false;;

let positive lit = not(negative lit);;

let negate = function (Not p) -> p | p -> Not p;;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec nnf fm =
  match fm with
  | And(p,q) -> And(nnf p,nnf q)
  | Or(p,q) -> Or(nnf p,nnf q)
  | Imp(p,q) -> Or(nnf(Not p),nnf q)
  | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
  | Not(Not p) -> nnf p
  | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
  | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
  | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
  | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Roll in simplification.                                                   *)
(* ------------------------------------------------------------------------- *)

let nnf fm = nnf(psimplify fm);;

(* ------------------------------------------------------------------------- *)
(* Example of NNF function in action.                                        *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<(p <=> q) <=> ~(r ==> s)>>;;

let fm' = nnf fm;;

tautology(Iff(fm,fm'));;
*)

(* ------------------------------------------------------------------------- *)
(* Simple negation-pushing when we don't care to distinguish occurrences.    *)
(* ------------------------------------------------------------------------- *)

let rec nenf fm =
  match fm with
    Not(Not p) -> nenf p
  | Not(And(p,q)) -> Or(nenf(Not p),nenf(Not q))
  | Not(Or(p,q)) -> And(nenf(Not p),nenf(Not q))
  | Not(Imp(p,q)) -> And(nenf p,nenf(Not q))
  | Not(Iff(p,q)) -> Iff(nenf p,nenf(Not q))
  | And(p,q) -> And(nenf p,nenf q)
  | Or(p,q) -> Or(nenf p,nenf q)
  | Imp(p,q) -> Or(nenf(Not p),nenf q)
  | Iff(p,q) -> Iff(nenf p,nenf q)
  | _ -> fm;;

let nenf fm = nenf(psimplify fm);;

(* ------------------------------------------------------------------------- *)
(* Some tautologies remarked on.                                             *)
(* ------------------------------------------------------------------------- *)

(*
tautology <<(p ==> p') /\ (q ==> q') ==> (p /\ q ==> p' /\ q')>>;;
tautology <<(p ==> p') /\ (q ==> q') ==> (p \/ q ==> p' \/ q')>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Disjunctive normal form (DNF) via truth tables.                           *)
(* ------------------------------------------------------------------------- *)

let list_conj l = if l = [] then True else end_itlist mk_and l;;

let list_disj l = if l = [] then False else end_itlist mk_or l;;

let mk_lits pvs v =
  list_conj (map (fun p -> if eval p v then p else Not p) pvs);;

let rec allsatvaluations subfn v pvs =
  match pvs with
    [] -> if subfn v then [v] else []
  | p::ps -> let v' t q = if q = p then t else v(q) in
             allsatvaluations subfn (v' false) ps @
             allsatvaluations subfn (v' true) ps;;

let dnf fm =
  let pvs = atoms fm in
  let satvals = allsatvaluations (eval fm) (fun s -> false) pvs in
  list_disj (map (mk_lits (map (fun p -> Atom p) pvs)) satvals);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<(p \/ q /\ r) /\ (~p \/ ~r)>>;;

dnf fm;;

print_truthtable fm;;

dnf <<p /\ q /\ r /\ s /\ t /\ u \/ u /\ v>>;;
*)

(* ------------------------------------------------------------------------- *)
(* DNF via distribution.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec distrib fm =
  match fm with
    And(p,(Or(q,r))) -> Or(distrib(And(p,q)),distrib(And(p,r)))
  | And(Or(p,q),r) -> Or(distrib(And(p,r)),distrib(And(q,r)))
  | _ -> fm;;

let rec rawdnf fm =
  match fm with
    And(p,q) -> distrib(And(rawdnf p,rawdnf q))
  | Or(p,q) -> Or(rawdnf p,rawdnf q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
rawdnf <<(p \/ q /\ r) /\ (~p \/ ~r)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* A version using a list representation.                                    *)
(* ------------------------------------------------------------------------- *)

let distrib s1 s2 = setify(allpairs union s1 s2);;

let rec purednf fm =
  match fm with
    And(p,q) -> distrib (purednf p) (purednf q)
  | Or(p,q) -> union (purednf p) (purednf q)
  | _ -> [[fm]];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
purednf <<(p \/ q /\ r) /\ (~p \/ ~r)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Filtering out trivial disjuncts (in this guise, contradictory).           *)
(* ------------------------------------------------------------------------- *)

let trivial lits =
  let pos,neg = partition positive lits in
  intersect pos (image negate neg) <> [];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
filter (non trivial) (purednf fm);;
*)

(* ------------------------------------------------------------------------- *)
(* With subsumption checking, done very naively (quadratic).                 *)
(* ------------------------------------------------------------------------- *)

let simpdnf fm =
  if fm = False then [] else if fm = True then [[]] else
  let djs = filter (non trivial) (purednf(nnf fm)) in
  filter (fun d -> not(exists (fun d' -> psubset d' d) djs)) djs;;

(* ------------------------------------------------------------------------- *)
(* Mapping back to a formula.                                                *)
(* ------------------------------------------------------------------------- *)

let dnf fm = list_disj(map list_conj (simpdnf fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<(p \/ q /\ r) /\ (~p \/ ~r)>>;;
dnf fm;;
tautology(Iff(fm,dnf fm));;
*)

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form (CNF) by essentially the same code.               *)
(* ------------------------------------------------------------------------- *)

let purecnf fm = image (image negate) (purednf(nnf(Not fm)));;

let simpcnf fm =
  if fm = False then [[]] else if fm = True then [] else
  let cjs = filter (non trivial) (purecnf fm) in
  filter (fun c -> not(exists (fun c' -> psubset c' c) cjs)) cjs;;

let cnf fm = list_conj(map list_disj (simpcnf fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<(p \/ q /\ r) /\ (~p \/ ~r)>>;;
cnf fm;;
tautology(Iff(fm,cnf fm));;
*)
(* ========================================================================= *)
(* Some propositional formulas to test, and functions to generate classes.   *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t) *)
(* ------------------------------------------------------------------------- *)

let ramsey s t n =
  let vertices = 1 -- n in
  let yesgrps = map (allsets 2) (allsets s vertices)
  and nogrps = map (allsets 2) (allsets t vertices) in
  let e[m;n] = Atom(P("p_"^(string_of_int m)^"_"^(string_of_int n))) in
  Or(list_disj (map (list_conj ** map e) yesgrps),
     list_disj (map (list_conj ** map (fun p -> Not(e p))) nogrps));;

(* ------------------------------------------------------------------------- *)
(* Some currently tractable examples.                                        *)
(* ------------------------------------------------------------------------- *)

(*
ramsey 3 3 4;;

tautology(ramsey 3 3 5);;

tautology(ramsey 3 3 6);;

*)

(* ------------------------------------------------------------------------- *)
(* Half adder.                                                               *)
(* ------------------------------------------------------------------------- *)

let halfsum x y = Iff(x,Not y);;

let halfcarry x y = And(x,y);;

let ha x y s c = And(Iff(s,halfsum x y),Iff(c,halfcarry x y));;

(* ------------------------------------------------------------------------- *)
(* Full adder.                                                               *)
(* ------------------------------------------------------------------------- *)

let carry x y z = Or(And(x,y),And(Or(x,y),z));;

let sum x y z = halfsum (halfsum x y) z;;

let fa x y z s c = And(Iff(s,sum x y z),Iff(c,carry x y z));;

(* ------------------------------------------------------------------------- *)
(* Useful idiom.                                                             *)
(* ------------------------------------------------------------------------- *)

let conjoin f l = list_conj (map f l);;

(* ------------------------------------------------------------------------- *)
(* n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      *)
(* ------------------------------------------------------------------------- *)

let ripplecarry x y c out n =
  conjoin (fun i -> fa (x i) (y i) (c i) (out i) (c(i + 1)))
          (0 -- (n - 1));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

let mk_index x i = Atom(P(x^"_"^(string_of_int i)))
and mk_index2 x i j =
  Atom(P(x^"_"^(string_of_int i)^"_"^(string_of_int j)));;

(*

let [x; y; out; c] = map mk_index ["X"; "Y"; "OUT"; "C"];;

ripplecarry x y c out 2;;

*)

(* ------------------------------------------------------------------------- *)
(* Special case with 0 instead of c(0).                                      *)
(* ------------------------------------------------------------------------- *)

let ripplecarry0 x y c out n =
  psimplify
   (ripplecarry x y (fun i -> if i = 0 then False else c i) out n);;

(* ------------------------------------------------------------------------- *)
(* Carry-select adder                                                        *)
(* ------------------------------------------------------------------------- *)

let ripplecarry1 x y c out n =
  psimplify
   (ripplecarry x y (fun i -> if i = 0 then True else c i) out n);;

let mux sel in0 in1 = Or(And(Not sel,in0),And(sel,in1));;

let offset n x i = x(n + i);;

let rec carryselect x y c0 c1 s0 s1 c s n k =
  let k' = min n k in
  let fm =
    And(And(ripplecarry0 x y c0 s0 k',ripplecarry1 x y c1 s1 k'),
        And(Iff(c k',mux (c 0) (c0 k') (c1 k')),
            conjoin (fun i -> Iff(s i,mux (c 0) (s0 i) (s1 i)))
                    (0 -- (k' - 1)))) in
  if k' < k then fm else
  And(fm,carryselect
            (offset k x) (offset k y) (offset k c0) (offset k c1)
            (offset k s0) (offset k s1) (offset k c) (offset k s)
            (n - k) k);;

(* ------------------------------------------------------------------------- *)
(* Equivalence problems for carry-select vs ripple carry adders.             *)
(* ------------------------------------------------------------------------- *)

let mk_adder_test n k =
  let [x; y; c; s; c0; s0; c1; s1; c2; s2] = map mk_index
      ["x"; "y"; "c"; "s"; "c0"; "s0"; "c1"; "s1"; "c2"; "s2"] in
  Imp(And(And(carryselect x y c0 c1 s0 s1 c s n k,Not(c 0)),
          ripplecarry0 x y c2 s2 n),
      And(Iff(c n,c2 n),
          conjoin (fun i -> Iff(s i,s2 i)) (0 -- (n - 1))));;

(* ------------------------------------------------------------------------- *)
(* Ripple carry stage that separates off the final result.                   *)
(*                                                                           *)
(*       UUUUUUUUUUUUUUUUUUUU  (u)                                           *)
(*    +  VVVVVVVVVVVVVVVVVVVV  (v)                                           *)
(*                                                                           *)
(*    = WWWWWWWWWWWWWWWWWWWW   (w)                                           *)
(*    +                     Z  (z)                                           *)
(* ------------------------------------------------------------------------- *)

let rippleshift u v c z w n =
  ripplecarry0 u v (fun i -> if i = n then w(n - 1) else c(i + 1))
                   (fun i -> if i = 0 then z else w(i - 1)) n;;

(* ------------------------------------------------------------------------- *)
(* Naive multiplier based on repeated ripple carry.                          *)
(* ------------------------------------------------------------------------- *)

let multiplier x u v out n =
  if n = 1 then And(Iff(out 0,x 0 0),Not(out 1)) else
  psimplify
   (And(Iff(out 0,x 0 0),
        And(rippleshift
               (fun i -> if i = n - 1 then False else x 0 (i + 1))
               (x 1) (v 2) (out 1) (u 2) n,
            if n = 2 then And(Iff(out 2,u 2 0),Iff(out 3,u 2 1)) else
            conjoin (fun k -> rippleshift (u k) (x k) (v(k + 1)) (out k)
                                (if k = n - 1 then fun i -> out(n + i)
                                 else u(k + 1)) n) (2 -- (n - 1)))));;

(* ------------------------------------------------------------------------- *)
(* Primality examples.                                                       *)
(* For large examples, should use "num" instead of "int" in these functions. *)
(* ------------------------------------------------------------------------- *)

let rec bitlength x = if x = 0 then 0 else 1 + bitlength (x / 2);;

let rec bit n x = if n = 0 then x mod 2 = 1 else bit (n - 1) (x / 2);;

let congruent_to x m n =
  conjoin (fun i -> if bit i m then x i else Not(x i))
          (0 -- (n - 1));;

let prime p =
  let [x; y; out] = map mk_index ["x"; "y"; "out"] in
  let m i j = And(x i,y j)
  and [u; v] = map mk_index2 ["u"; "v"] in
  let n = bitlength p in
  Not(And(multiplier m u v out (n - 1),
      congruent_to out p (max n (2 * n - 2))));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*

tautology(prime 7);;
tautology(prime 9);;
tautology(prime 11);;

*)
(* ========================================================================= *)
(* Definitional CNF.                                                         *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(*
cnf <<p <=> (q <=> r)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Make a stylized variable and update the index.                            *)
(* ------------------------------------------------------------------------- *)

let mkprop n = Atom(P("p_"^(string_of_num n))),n +/ Int 1;;

(* ------------------------------------------------------------------------- *)
(* Core definitional CNF procedure.                                          *)
(* ------------------------------------------------------------------------- *)

let rec maincnf (fm,defs,n as trip) =
  match fm with
    And(p,q) -> defstep mk_and (p,q) trip
  | Or(p,q) -> defstep mk_or (p,q) trip
  | Iff(p,q) -> defstep mk_iff (p,q) trip
  | _ -> trip

and defstep op (p,q) (fm,defs,n) =
  let fm1,defs1,n1 = maincnf (p,defs,n) in
  let fm2,defs2,n2 = maincnf (q,defs1,n1) in
  let fm' = op fm1 fm2 in
  try (fst(apply defs2 fm'),defs2,n2) with Failure _ ->
  let v,n3 = mkprop n2 in (v,(fm'|->(v,Iff(v,fm'))) defs2,n3);;

(* ------------------------------------------------------------------------- *)
(* Make n large enough that "v_m" won't clash with s for any m >= n          *)
(* ------------------------------------------------------------------------- *)

let max_varindex pfx =
  let m = String.length pfx in
  fun s n ->
    let l = String.length s in
    if l <= m or String.sub s 0 m <> pfx then n else
    let s' = String.sub s m (l - m) in
    if forall numeric (explode s') then max_num n (num_of_string s')
    else n;;

(* ------------------------------------------------------------------------- *)
(* Overall definitional CNF.                                                 *)
(* ------------------------------------------------------------------------- *)

let mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = Int 1 +/ overatoms (max_varindex "p_" ** pname) fm' (Int 0) in
  let (fm'',defs,_) = fn (fm',undefined,n) in
  let deflist = map (snd ** snd) (graph defs) in
  unions(simpcnf fm'' :: map simpcnf deflist);;

let defcnf fm = list_conj(map list_disj(mk_defcnf maincnf fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Version tweaked to exploit initial structure.                             *)
(* ------------------------------------------------------------------------- *)

let subcnf sfn op (p,q) (fm,defs,n) =
  let fm1,defs1,n1 = sfn(p,defs,n) in
  let fm2,defs2,n2 = sfn(q,defs1,n1) in (op fm1 fm2,defs2,n2);;

let rec orcnf (fm,defs,n as trip) =
  match fm with
    Or(p,q) -> subcnf orcnf mk_or (p,q) trip
  | _ -> maincnf trip;;

let rec andcnf (fm,defs,n as trip) =
  match fm with
    And(p,q) -> subcnf andcnf mk_and (p,q) trip
  | _ -> orcnf trip;;

let defcnfs fm = mk_defcnf andcnf fm;;

let defcnf fm = list_conj (map list_disj (defcnfs fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Version that guarantees 3-CNF.                                            *)
(* ------------------------------------------------------------------------- *)

let rec andcnf3 (fm,defs,n as trip) =
  match fm with
    And(p,q) -> subcnf andcnf3 mk_and (p,q) trip
  | _ -> maincnf trip;;

let defcnf3 fm = list_conj (map list_disj(mk_defcnf andcnf3 fm));;
(* ========================================================================= *)
(* The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The DP procedure.                                                         *)
(* ------------------------------------------------------------------------- *)

let one_literal_rule clauses =
  let u = hd (find (fun cl -> length cl = 1) clauses) in
  let u' = negate u in
  let clauses1 = filter (fun cl -> not (mem u cl)) clauses in
  image (fun cl -> subtract cl [u']) clauses1;;

let affirmative_negative_rule clauses =
  let neg',pos = partition negative (unions clauses) in
  let neg = image negate neg' in
  let pos_only = subtract pos neg and neg_only = subtract neg pos in
  let pure = union pos_only (image negate neg_only) in
  if pure = [] then failwith "affirmative_negative_rule" else
  filter (fun cl -> intersect cl pure = []) clauses;;

let resolve_on p clauses =
  let p' = negate p and pos,notpos = partition (mem p) clauses in
  let neg,other = partition (mem p') notpos in
  let pos' = image (filter (fun l -> l <> p)) pos
  and neg' = image (filter (fun l -> l <> p')) neg in
  let res0 = allpairs union pos' neg' in
  union other (filter (non trivial) res0);;

let resolution_blowup cls l =
  let m = length(filter (mem l) cls)
  and n = length(filter (mem (negate l)) cls) in
  m * n - m - n;;

let resolution_rule clauses =
  let pvs = filter positive (unions clauses) in
  let p = minimize (resolution_blowup clauses) pvs in
  resolve_on p clauses;;

(* ------------------------------------------------------------------------- *)
(* Overall procedure.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec dp clauses =
  if clauses = [] then true else if mem [] clauses then false else
  try dp (one_literal_rule clauses) with Failure _ ->
  try dp (affirmative_negative_rule clauses) with Failure _ ->
  dp(resolution_rule clauses);;

(* ------------------------------------------------------------------------- *)
(* Davis-Putnam satisfiability tester and tautology checker.                 *)
(* ------------------------------------------------------------------------- *)

let dpsat fm = dp(defcnfs fm);;

let dptaut fm = not(dpsat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
tautology(prime 11);;

dptaut(prime 11);;
*)

(* ------------------------------------------------------------------------- *)
(* The same thing but with the DPLL procedure.                               *)
(* ------------------------------------------------------------------------- *)

let posneg_count cls l =                         
  let m = length(filter (mem l) cls)                 
  and n = length(filter (mem (negate l)) cls) in
  m + n;;                                  

let rec dpll clauses =       
  if clauses = [] then true else if mem [] clauses then false else
  try dpll(one_literal_rule clauses) with Failure _ ->
  try dpll(affirmative_negative_rule clauses) with Failure _ ->
  let pvs = filter positive (unions clauses) in
  let p = maximize (posneg_count clauses) pvs in
  dpll (insert [p] clauses) or dpll (insert [negate p] clauses);;
                                                     
let dpllsat fm = dpll(defcnfs fm);;

let dplltaut fm = not(dpllsat(Not fm));;                   

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
dplltaut(prime 11);;
*)

(* ------------------------------------------------------------------------- *)
(* Iterative implementation with explicit trail instead of recursion.        *)
(* ------------------------------------------------------------------------- *)

type trailmix = Guessed | Deduced;;

let unassigned =
  let litabs p = match p with Not q -> q | _ -> p in
  fun cls trail -> subtract (unions(image (image litabs) cls))
                            (image (litabs ** fst) trail);;

let rec unit_subpropagate (cls,fn,trail) =
  let cls' = map (filter ((not) ** defined fn ** negate)) cls in
  let uu = function [c] when not(defined fn c) -> [c] | _ -> failwith "" in
  let newunits = unions(mapfilter uu cls') in
  if newunits = [] then (cls',fn,trail) else
  let trail' = itlist (fun p t -> (p,Deduced)::t) newunits trail
  and fn' = itlist (fun u -> (u |-> ())) newunits fn in
  unit_subpropagate (cls',fn',trail');;

let unit_propagate (cls,trail) =
  let fn = itlist (fun (x,_) -> (x |-> ())) trail undefined in
  let cls',fn',trail' = unit_subpropagate (cls,fn,trail) in cls',trail';;

let rec backtrack trail =
  match trail with
    (p,Deduced)::tt -> backtrack tt
  | _ -> trail;;

let rec dpli cls trail =
  let cls',trail' = unit_propagate (cls,trail) in
  if mem [] cls' then
    match backtrack trail with
      (p,Guessed)::tt -> dpli cls ((negate p,Deduced)::tt)
    | _ -> false
  else
      match unassigned cls trail' with
        [] -> true
      | ps -> let p = maximize (posneg_count cls') ps in
              dpli cls ((p,Guessed)::trail');;

let dplisat fm = dpli (defcnfs fm) [];;

let dplitaut fm = not(dplisat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* With simple non-chronological backjumping and learning.                   *)
(* ------------------------------------------------------------------------- *)

let rec backjump cls p trail =
  match backtrack trail with
    (q,Guessed)::tt ->
        let cls',trail' = unit_propagate (cls,(p,Guessed)::tt) in
        if mem [] cls' then backjump cls p tt else trail
  | _ -> trail;;

let rec dplb cls trail =
  let cls',trail' = unit_propagate (cls,trail) in
  if mem [] cls' then
    match backtrack trail with
      (p,Guessed)::tt ->
        let trail' = backjump cls p tt in
        let declits = filter (fun (_,d) -> d = Guessed) trail' in
        let conflict = insert (negate p) (image (negate ** fst) declits) in
        dplb (conflict::cls) ((negate p,Deduced)::trail')
    | _ -> false
  else
    match unassigned cls trail' with
      [] -> true
    | ps -> let p = maximize (posneg_count cls') ps in
            dplb cls ((p,Guessed)::trail');;

let dplbsat fm = dplb (defcnfs fm) [];;

let dplbtaut fm = not(dplbsat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
dplitaut(prime 101);;
dplbtaut(prime 101);;
*)
(* ========================================================================= *)
(* Simple implementation of Stalmarck's algorithm.                           *)
(*                                                                           *)
(* NB! This algorithm is patented for commercial use (not that a toy version *)
(* like this would actually be useful in practice).                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Triplet transformation, using functions defined earlier.                  *)
(* ------------------------------------------------------------------------- *)

let triplicate fm =
  let fm' = nenf fm in
  let n = Int 1 +/ overatoms (max_varindex "p_" ** pname) fm' (Int 0) in
  let (p,defs,_) = maincnf (fm',undefined,n) in
  p,map (snd ** snd) (graph defs);;

(* ------------------------------------------------------------------------- *)
(* Automatically generate triggering rules to save writing them out.         *)
(* ------------------------------------------------------------------------- *)

let atom lit = if negative lit then negate lit else lit;;

let rec align (p,q) =
  if atom p < atom q then align (q,p) else
  if negative p then (negate p,negate q) else (p,q);;

let equate2 (p,q) eqv = equate (negate p,negate q) (equate (p,q) eqv);;

let rec irredundant rel eqs =
  match eqs with
    [] -> []
  | (p,q)::oth ->
      if canonize rel p = canonize rel q then irredundant rel oth
      else insert (p,q) (irredundant (equate2 (p,q) rel) oth);;

let consequences (p,q as peq) fm eqs =
  let follows(r,s) = tautology(Imp(And(Iff(p,q),fm),Iff(r,s))) in
  irredundant (equate2 peq unequal) (filter follows eqs);;

let triggers fm =
  let poslits = insert True (map (fun p -> Atom p) (atoms fm)) in
  let lits = union poslits (map negate poslits) in
  let pairs = allpairs (fun p q -> p,q) lits lits in
  let npairs = filter (fun (p,q) -> atom p <> atom q) pairs in
  let eqs = setify(map align npairs) in
  let raw = map (fun p -> p,consequences p fm eqs) eqs in
  filter (fun (p,c) -> c <> []) raw;;

(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

(*
triggers <<p <=> (q /\ r)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Precompute and instantiate triggers for standard triplets.                *)
(* ------------------------------------------------------------------------- *)

let trigger =
  let [trig_and; trig_or; trig_imp; trig_iff] = map triggers
      [<<p <=> q /\ r>>; <<p <=> q \/ r>>;
       <<p <=> (q ==> r)>>; <<p <=> (q <=> r)>>]
  and p = <<p>> and q = <<q>> and r = <<r>>
  and ddnegate fm = match fm with Not(Not p) -> p | _ -> fm in
  let inst_fn [x;y;z] =
    let subfn = fpf [P"p"; P"q"; P"r"] [x; y; z] in
    ddnegate ** psubst subfn in
  let inst2_fn i (p,q) = align(inst_fn i p,inst_fn i q) in
  let instn_fn i (a,c) = inst2_fn i a,map (inst2_fn i) c in
  let inst_trigger = map ** instn_fn in
  function (Iff(x,And(y,z))) -> inst_trigger [x;y;z] trig_and
         | (Iff(x,Or(y,z))) -> inst_trigger [x;y;z] trig_or
         | (Iff(x,Imp(y,z))) -> inst_trigger [x;y;z] trig_imp
         | (Iff(x,Iff(y,z))) -> inst_trigger [x;y;z] trig_iff;;

(* ------------------------------------------------------------------------- *)
(* Compute a function mapping each variable/true to relevant triggers.       *)
(* ------------------------------------------------------------------------- *)

let relevance trigs =
  let insert_relevant p trg f = (p |-> insert trg (tryapplyl f p)) f in
  let insert_relevant2 ((p,q),_ as trg) f =
    insert_relevant p trg (insert_relevant q trg f) in
  itlist insert_relevant2 trigs undefined;;

(* ------------------------------------------------------------------------- *)
(* Merging of equiv classes and relevancies.                                 *)
(* ------------------------------------------------------------------------- *)

let equatecons (p0,q0) (eqv,rfn as erf) =
  let p = canonize eqv p0 and q = canonize eqv q0 in
  if p = q then [],erf else
  let p' = canonize eqv (negate p0) and q' = canonize eqv (negate q0) in
  let eqv' = equate2(p,q) eqv
  and sp_pos = tryapplyl rfn p and sp_neg = tryapplyl rfn p'
  and sq_pos = tryapplyl rfn q and sq_neg = tryapplyl rfn q' in
  let rfn' =
    (canonize eqv' p |-> union sp_pos sq_pos)
    ((canonize eqv' p' |-> union sp_neg sq_neg) rfn) in
  let nw = union (intersect sp_pos sq_pos) (intersect sp_neg sq_neg) in
  itlist (union ** snd) nw [],(eqv',rfn');;

(* ------------------------------------------------------------------------- *)
(* Zero-saturation given an equivalence/relevance and new assignments.       *)
(* ------------------------------------------------------------------------- *)

let rec zero_saturate erf assigs =
  match assigs with
    [] -> erf
  | (p,q)::ts -> let news,erf' = equatecons (p,q) erf in
                 zero_saturate erf' (union ts news);;

(* ------------------------------------------------------------------------- *)
(* Zero-saturate then check for contradictoriness.                           *)
(* ------------------------------------------------------------------------- *)

let zero_saturate_and_check erf trigs =
  let (eqv',rfn' as erf') = zero_saturate erf trigs in
  let vars = filter positive (equated eqv') in
  if exists (fun x -> canonize eqv' x = canonize eqv' (Not x)) vars
  then snd(equatecons (True,Not True) erf') else erf';;

(* ------------------------------------------------------------------------- *)
(* Now we can quickly test for contradiction.                                *)
(* ------------------------------------------------------------------------- *)

let truefalse pfn = canonize pfn (Not True) = canonize pfn True;;

(* ------------------------------------------------------------------------- *)
(* Iterated equivalening over a set.                                         *)
(* ------------------------------------------------------------------------- *)

let rec equateset s0 eqfn =
  match s0 with
    a::(b::s2 as s1) -> equateset s1 (snd(equatecons (a,b) eqfn))
  | _ -> eqfn;;

(* ------------------------------------------------------------------------- *)
(* Intersection operation on equivalence classes and relevancies.            *)
(* ------------------------------------------------------------------------- *)

let rec inter els (eq1,_ as erf1) (eq2,_ as erf2) rev1 rev2 erf =
  match els with
    [] -> erf
  | x::xs ->
      let b1 = canonize eq1 x and b2 = canonize eq2 x in
      let s1 = apply rev1 b1 and s2 = apply rev2 b2 in
      let s = intersect s1 s2 in
      inter (subtract xs s) erf1 erf2 rev1 rev2 (equateset s erf);;

(* ------------------------------------------------------------------------- *)
(* Reverse the equivalence mappings.                                         *)
(* ------------------------------------------------------------------------- *)

let reverseq domain eqv =
  let al = map (fun x -> x,canonize eqv x) domain in
  itlist (fun (y,x) f -> (x |-> insert y (tryapplyl f x)) f)
         al undefined;;

(* ------------------------------------------------------------------------- *)
(* Special intersection taking contradictoriness into account.               *)
(* ------------------------------------------------------------------------- *)

let stal_intersect (eq1,_ as erf1) (eq2,_ as erf2) erf =
  if truefalse eq1 then erf2 else if truefalse eq2 then erf1 else
  let dom1 = equated eq1 and dom2 = equated eq2 in
  let comdom = intersect dom1 dom2 in
  let rev1 = reverseq dom1 eq1 and rev2 = reverseq dom2 eq2 in
  inter comdom erf1 erf2 rev1 rev2 erf;;

(* ------------------------------------------------------------------------- *)
(* General n-saturation for n >= 1                                           *)
(* ------------------------------------------------------------------------- *)

let rec saturate n erf assigs allvars =
  let (eqv',_ as erf') = zero_saturate_and_check erf assigs in
  if n = 0 or truefalse eqv' then erf' else
  let (eqv'',_ as erf'') = splits n erf' allvars allvars in
  if eqv'' = eqv' then erf'' else saturate n erf'' [] allvars

and splits n (eqv,_ as erf) allvars vars =
  match vars with
    [] -> erf
  | p::ovars ->
        if canonize eqv p <> p then splits n erf allvars ovars else
        let erf0 = saturate (n - 1) erf [p,Not True] allvars
        and erf1 = saturate (n - 1) erf [p,True] allvars in
        let (eqv',_ as erf') = stal_intersect erf0 erf1 erf in
        if truefalse eqv' then erf' else splits n erf' allvars ovars;;

(* ------------------------------------------------------------------------- *)
(* Saturate up to a limit.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec saturate_upto vars n m trigs assigs =
  if n > m then failwith("Not "^(string_of_int m)^"-easy") else
   (print_string("*** Starting "^(string_of_int n)^"-saturation");
    print_newline();
    let (eqv,_) = saturate n (unequal,relevance trigs) assigs vars in
    truefalse eqv or saturate_upto vars (n + 1) m trigs assigs);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let stalmarck fm =
  let include_trig (e,cqs) f = (e |-> union cqs (tryapplyl f e)) f in
  let fm' = psimplify(Not fm) in
  if fm' = False then true else if fm' = True then false else
  let p,triplets = triplicate fm' in
  let trigfn = itlist (itlist include_trig ** trigger)
                      triplets undefined
  and vars = map (fun p -> Atom p) (unions(map atoms triplets)) in
  saturate_upto vars 0 2 (graph trigfn) [p,True];;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
time stalmarck (mk_adder_test 6 3);;
*)
(* ========================================================================= *)
(* Binary decision diagrams (BDDs) using complement edges.                   *)
(*                                                                           *)
(* In practice one would use hash tables, but we use abstract finite         *)
(* partial functions here. They might also look nicer imperatively.          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type bddnode = prop * int * int;;

(* ------------------------------------------------------------------------- *)
(* A BDD contains a variable order, unique and computed table.               *)
(* ------------------------------------------------------------------------- *)

type bdd = Bdd of ((bddnode,int)func * (int,bddnode)func * int) *
                  (prop->prop->bool);;

let print_bdd (Bdd((unique,uback,n),ord)) =
  print_string ("<BDD with "^(string_of_int n)^" nodes>");;

#install_printer print_bdd;;

(* ------------------------------------------------------------------------- *)
(* Map a BDD node back to its components.                                    *)
(* ------------------------------------------------------------------------- *)

let expand_node (Bdd((_,expand,_),_)) n =
  if n >= 0 then tryapplyd expand n (P"",1,1)
  else let (p,l,r) = tryapplyd expand (-n) (P"",1,1) in (p,-l,-r);;

(* ------------------------------------------------------------------------- *)
(* Lookup or insertion if not there in unique table.                         *)
(* ------------------------------------------------------------------------- *)

let lookup_unique (Bdd((unique,expand,n),ord) as bdd) node =
  try bdd,apply unique node with Failure _ ->
  Bdd(((node|->n) unique,(n|->node) expand,n+1),ord),n;;

(* ------------------------------------------------------------------------- *)
(* Produce a BDD node (old or new).                                          *)
(* ------------------------------------------------------------------------- *)

let mk_node bdd (s,l,r) =
  if l = r then bdd,l
  else if l >= 0 then lookup_unique bdd (s,l,r)
  else let bdd',n = lookup_unique bdd (s,-l,-r) in bdd',-n;;

(* ------------------------------------------------------------------------- *)
(* Create a new BDD with a given ordering.                                   *)
(* ------------------------------------------------------------------------- *)

let mk_bdd ord = Bdd((undefined,undefined,2),ord);;

(* ------------------------------------------------------------------------- *)
(* Extract the ordering field of a BDD.                                      *)
(* ------------------------------------------------------------------------- *)

let order (Bdd(_,ord)) p1 p2 = (p2 = P"" & p1 <> P"") or ord p1 p2;;

(* ------------------------------------------------------------------------- *)
(* Threading state through.                                                  *)
(* ------------------------------------------------------------------------- *)

let thread s g (f1,x1) (f2,x2) =
  let s',y1 = f1 s x1 in let s'',y2 = f2 s' x2 in g s'' (y1,y2);;

(* ------------------------------------------------------------------------- *)
(* Perform an AND operation on BDDs, maintaining canonicity.                 *)
(* ------------------------------------------------------------------------- *)

let rec bdd_and (bdd,comp as bddcomp) (m1,m2) =
  if m1 = -1 or m2 = -1 then bddcomp,-1
  else if m1 = 1 then bddcomp,m2 else if m2 = 1 then bddcomp,m1 else
  try bddcomp,apply comp (m1,m2) with Failure _ ->
  try  bddcomp,apply comp (m2,m1) with Failure _ ->
  let (p1,l1,r1) = expand_node bdd m1
  and (p2,l2,r2) = expand_node bdd m2 in
  let (p,lpair,rpair) =
      if p1 = p2 then p1,(l1,l2),(r1,r2)
      else if order bdd p1 p2 then p1,(l1,m2),(r1,m2)
      else p2,(m1,l2),(m1,r2) in
  let (bdd',comp'),(lnew,rnew) =
    thread bddcomp (fun s z -> s,z) (bdd_and,lpair) (bdd_and,rpair) in
  let bdd'',n = mk_node bdd' (p,lnew,rnew) in
  (bdd'',((m1,m2) |-> n) comp'),n;;

(* ------------------------------------------------------------------------- *)
(* The other binary connectives.                                             *)
(* ------------------------------------------------------------------------- *)

let bdd_or bdc (m1,m2) = let bdc1,n = bdd_and bdc (-m1,-m2) in bdc1,-n;;

let bdd_imp bdc (m1,m2) = bdd_or bdc (-m1,m2);;

let bdd_iff bdc (m1,m2) =
  thread bdc bdd_or (bdd_and,(m1,m2)) (bdd_and,(-m1,-m2));;

(* ------------------------------------------------------------------------- *)
(* Formula to BDD conversion.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mkbdd (bdd,comp as bddcomp) fm =
  match fm with
    False -> bddcomp,-1
  | True -> bddcomp,1
  | Atom(s) -> let bdd',n = mk_node bdd (s,1,-1) in (bdd',comp),n
  | Not(p) -> let bddcomp',n = mkbdd bddcomp p in bddcomp',-n
  | And(p,q) -> thread bddcomp bdd_and (mkbdd,p) (mkbdd,q)
  | Or(p,q) -> thread bddcomp bdd_or (mkbdd,p) (mkbdd,q)
  | Imp(p,q) -> thread bddcomp bdd_imp (mkbdd,p) (mkbdd,q)
  | Iff(p,q) -> thread bddcomp bdd_iff (mkbdd,p) (mkbdd,q);;

(* ------------------------------------------------------------------------- *)
(* Tautology checking using BDDs.                                            *)
(* ------------------------------------------------------------------------- *)

let bddtaut fm = snd(mkbdd (mk_bdd (<),undefined) fm) = 1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
bddtaut (mk_adder_test 4 2);;
*)

(* ------------------------------------------------------------------------- *)
(* Towards a more intelligent treatment of "definitions".                    *)
(* ------------------------------------------------------------------------- *)

let dest_nimp fm = match fm with Not(p) -> p,False | _ -> dest_imp fm;;

let rec dest_iffdef fm =
  match fm with
    Iff(Atom(x),r) | Iff(r,Atom(x)) -> x,r
  | _ -> failwith "not a defining equivalence";;

let restore_iffdef (x,e) fm = Imp(Iff(Atom(x),e),fm);;

let suitable_iffdef defs (x,q) =
  let fvs = atoms q in not (exists (fun (x',_) -> mem x' fvs) defs);;

let rec sort_defs acc defs fm =
  try let (x,e) = find (suitable_iffdef defs) defs in
      let ps,nonps = partition (fun (x',_) -> x' = x) defs in
      let ps' = subtract ps [x,e] in
      sort_defs ((x,e)::acc) nonps (itlist restore_iffdef ps' fm)
  with Failure _ -> rev acc,itlist restore_iffdef defs fm;;

(* ------------------------------------------------------------------------- *)
(* Improved setup.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec mkbdde sfn (bdd,comp as bddcomp) fm =
  match fm with
    False -> bddcomp,-1
  | True -> bddcomp,1
  | Atom(s) -> (try bddcomp,apply sfn s with Failure _ ->
                let bdd',n = mk_node bdd (s,1,-1) in (bdd',comp),n)
  | Not(p) -> let bddcomp',n = mkbdde sfn bddcomp p in bddcomp',-n
  | And(p,q) -> thread bddcomp bdd_and (mkbdde sfn,p) (mkbdde sfn,q)
  | Or(p,q) -> thread bddcomp bdd_or (mkbdde sfn,p) (mkbdde sfn,q)
  | Imp(p,q) -> thread bddcomp bdd_imp (mkbdde sfn,p) (mkbdde sfn,q)
  | Iff(p,q) -> thread bddcomp bdd_iff (mkbdde sfn,p) (mkbdde sfn,q);;

let rec mkbdds sfn bdd defs fm =
  match defs with
    [] -> mkbdde sfn bdd fm
  | (p,e)::odefs -> let bdd',b = mkbdde sfn bdd e in
                    mkbdds ((p |-> b) sfn) bdd' odefs fm;;

let ebddtaut fm =
  let l,r = try dest_nimp fm with Failure _ -> True,fm in
  let eqs,noneqs = partition (can dest_iffdef) (conjuncts l) in
  let defs,fm' = sort_defs [] (map dest_iffdef eqs)
                              (itlist mk_imp noneqs r) in
  snd(mkbdds undefined (mk_bdd (<),undefined) defs fm') = 1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
ebddtaut (prime 101);;

ebddtaut (mk_adder_test 9 5);;
*)
(* ========================================================================= *)
(* Basic stuff for first order logic.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Terms.                                                                    *)
(* ------------------------------------------------------------------------- *)

type term = Var of string
          | Fn of string * term list;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
Fn("sqrt",[Fn("-",[Fn("1",[]);
                   Fn("cos",[Fn("power",[Fn("+",[Var "x"; Var "y"]);
                                        Fn("2",[])])])])]);;
*)

(* ------------------------------------------------------------------------- *)
(* Abbreviation for FOL formula.                                             *)
(* ------------------------------------------------------------------------- *)

type fol = R of string * term list;;

(* ------------------------------------------------------------------------- *)
(* Special case of applying a subfunction to the top *terms*.                *)
(* ------------------------------------------------------------------------- *)

let onformula f = onatoms(fun (R(p,a)) -> Atom(R(p,map f a)));;

(* ------------------------------------------------------------------------- *)
(* Trivial example of "x + y < z".                                           *)
(* ------------------------------------------------------------------------- *)

(*
Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;
*)

(* ------------------------------------------------------------------------- *)
(* Parsing of terms.                                                         *)
(* ------------------------------------------------------------------------- *)

let is_const_name s = forall numeric (explode s) or s = "nil";;

let rec parse_atomic_term vs inp =
  match inp with
    [] -> failwith "term expected"
  | "("::rest -> parse_bracketed (parse_term vs) ")" rest
  | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
  | f::"("::")"::rest -> Fn(f,[]),rest
  | f::"("::rest ->
      papply (fun args -> Fn(f,args))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | a::rest ->
      (if is_const_name a & not(mem a vs) then Fn(a,[]) else Var a),rest

and parse_term vs inp =
  parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
    (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
       (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
          (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
             (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                   (parse_atomic_term vs)))))) inp;;

let parset = make_parser (parse_term []);;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas.                                                      *)
(* ------------------------------------------------------------------------- *)

let parse_infix_atom vs inp =       
  let tm,rest = parse_term vs inp in
  if exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then                     
        papply (fun tm' -> Atom(R(hd rest,[tm;tm'])))                          
               (parse_term vs (tl rest))                                       
  else failwith "";;
                                                               
let parse_atom vs inp =
  try parse_infix_atom vs inp with Failure _ ->                                
  match inp with                                                               
  | p::"("::")"::rest -> Atom(R(p,[])),rest                                    
  | p::"("::rest ->
      papply (fun args -> Atom(R(p,args)))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | p::rest when p <> "(" -> Atom(R(p,[])),rest
  | _ -> failwith "parse_atom";;
                                                                               
let parse = make_parser                                                        
  (parse_formula (parse_infix_atom,parse_atom) []);;              

(* ------------------------------------------------------------------------- *)
(* Set up parsing of quotations.                                             *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse;;

let secondary_parser = parset;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
<<(forall x. x < 2 ==> 2 * x <= 3) \/ false>>;;

<<|2 * x|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Printing of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec print_term prec fm =
  match fm with
    Var x -> print_string x
  | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
  | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
  | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
  | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
  | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
  | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
  | Fn(f,args) -> print_fargs f args

and print_fargs f args =
  print_string f;
  if args = [] then () else
   (print_string "(";
    open_box 0;
    print_term 0 (hd args); print_break 0 0;
    do_list (fun t -> print_string ","; print_break 0 0; print_term 0 t)
            (tl args);
    close_box();
    print_string ")")

and print_infix_term isleft oldprec newprec sym p q =
  if oldprec > newprec then (print_string "("; open_box 0) else ();
  print_term (if isleft then newprec else newprec+1) p;
  print_string sym;
  print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
  print_term (if isleft then newprec+1 else newprec) q;
  if oldprec > newprec then (close_box(); print_string ")") else ();;

let printert tm =
  open_box 0; print_string "<<|";
  open_box 0; print_term 0 tm; close_box();
  print_string "|>>"; close_box();;

#install_printer printert;;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas.                                                     *)
(* ------------------------------------------------------------------------- *)

let print_atom prec (R(p,args)) =
  if mem p ["="; "<"; "<="; ">"; ">="] & length args = 2
  then print_infix_term false 12 12 (" "^p) (el 0 args) (el 1 args)
  else print_fargs p args;;

let print_fol_formula = print_qformula print_atom;;

#install_printer print_fol_formula;;

(* ------------------------------------------------------------------------- *)
(* Examples in the main text.                                                *)
(* ------------------------------------------------------------------------- *)

(*
<<forall x y. exists z. x < z /\ y < z>>;;

<<~(forall x. P(x)) <=> exists y. ~P(y)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Semantics, implemented of course for finite domains only.                 *)
(* ------------------------------------------------------------------------- *)

let rec termval (domain,func,pred as m) v tm =
  match tm with
    Var(x) -> apply v x
  | Fn(f,args) -> func f (map (termval m v) args);;

let rec holds (domain,func,pred as m) v fm =
  match fm with
    False -> false
  | True -> true
  | Atom(R(r,args)) -> pred r (map (termval m v) args)
  | Not(p) -> not(holds m v p)
  | And(p,q) -> (holds m v p) & (holds m v q)
  | Or(p,q) -> (holds m v p) or (holds m v q)
  | Imp(p,q) -> not(holds m v p) or (holds m v q)
  | Iff(p,q) -> (holds m v p = holds m v q)
  | Forall(x,p) -> forall (fun a -> holds m ((x |-> a) v) p) domain
  | Exists(x,p) -> exists (fun a -> holds m ((x |-> a) v) p) domain;;

(* ------------------------------------------------------------------------- *)
(* Examples of particular interpretations.                                   *)
(* ------------------------------------------------------------------------- *)

let bool_interp =
  let func f args =
    match (f,args) with
      ("0",[]) -> false
    | ("1",[]) -> true
    | ("+",[x;y]) -> not(x = y)
    | ("*",[x;y]) -> x & y
    | _ -> failwith "uninterpreted function"
  and pred p args =
    match (p,args) with
      ("=",[x;y]) -> x = y
    | _ -> failwith "uninterpreted predicate" in
  ([false; true],func,pred);;

let mod_interp n =
  let func f args =
    match (f,args) with
      ("0",[]) -> 0
    | ("1",[]) -> 1 mod n
    | ("+",[x;y]) -> (x + y) mod n
    | ("*",[x;y]) -> (x * y) mod n
    | _ -> failwith "uninterpreted function"
  and pred p args =
    match (p,args) with
      ("=",[x;y]) -> x = y
    | _ -> failwith "uninterpreted predicate" in
  (0--(n-1),func,pred);;

(*
holds bool_interp undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 2) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 3) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

let fm = <<forall x. ~(x = 0) ==> exists y. x * y = 1>>;;

filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

holds (mod_interp 3) undefined <<(forall x. x = 0) ==> 1 = 0>>;;
holds (mod_interp 3) undefined <<forall x. x = 0 ==> 1 = 0>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Free variables in terms and formulas.                                     *)
(* ------------------------------------------------------------------------- *)

let rec fvt tm =
  match tm with
    Var x -> [x]
  | Fn(f,args) -> unions (map fvt args);;

let rec var fm =
   match fm with
    False | True -> []
  | Atom(R(p,args)) -> unions (map fvt args)
  | Not(p) -> var p
  | And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q) -> union (var p) (var q)
  | Forall(x,p) | Exists(x,p) -> insert x (var p);;

let rec fv fm =
  match fm with
    False | True -> []
  | Atom(R(p,args)) -> unions (map fvt args)
  | Not(p) -> fv p
  | And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q) -> union (fv p) (fv q)
  | Forall(x,p) | Exists(x,p) -> subtract (fv p) [x];;

(* ------------------------------------------------------------------------- *)
(* Universal closure of a formula.                                           *)
(* ------------------------------------------------------------------------- *)

let generalize fm = itlist mk_forall (fv fm) fm;;

(* ------------------------------------------------------------------------- *)
(* Substitution within terms.                                                *)
(* ------------------------------------------------------------------------- *)

let rec tsubst sfn tm =
  match tm with
    Var x -> tryapplyd sfn x tm
  | Fn(f,args) -> Fn(f,map (tsubst sfn) args);;

(* ------------------------------------------------------------------------- *)
(* Variant function and examples.                                            *)
(* ------------------------------------------------------------------------- *)

let rec variant x vars =
  if mem x vars then variant (x^"'") vars else x;;

(*
variant "x" ["y"; "z"];;

variant "x" ["x"; "y"];;

variant "x" ["x"; "x'"];;
*)

(* ------------------------------------------------------------------------- *)
(* Substitution in formulas, with variable renaming.                         *)
(* ------------------------------------------------------------------------- *)

let rec subst subfn fm =
  match fm with
    False -> False
  | True -> True
  | Atom(R(p,args)) -> Atom(R(p,map (tsubst subfn) args))
  | Not(p) -> Not(subst subfn p)
  | And(p,q) -> And(subst subfn p,subst subfn q)
  | Or(p,q) -> Or(subst subfn p,subst subfn q)
  | Imp(p,q) -> Imp(subst subfn p,subst subfn q)
  | Iff(p,q) -> Iff(subst subfn p,subst subfn q)
  | Forall(x,p) -> substq subfn mk_forall x p
  | Exists(x,p) -> substq subfn mk_exists x p

and substq subfn quant x p =
  let x' = if exists (fun y -> mem x (fvt(tryapplyd subfn y (Var y))))
                     (subtract (fv p) [x])
           then variant x (fv(subst (undefine x subfn) p)) else x in
  quant x' (subst ((x |-> Var x') subfn) p);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
subst ("y" |=> Var "x") <<forall x. x = y>>;;

subst ("y" |=> Var "x") <<forall x x'. x = y ==> x = x'>>;;
*)
(* ========================================================================= *)
(* Prenex and Skolem normal forms.                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Routine simplification. Like "psimplify" but with quantifier clauses.     *)
(* ------------------------------------------------------------------------- *)

let simplify1 fm =
  match fm with
    Forall(x,p) -> if mem x (fv p) then fm else p
  | Exists(x,p) -> if mem x (fv p) then fm else p
  | _ -> psimplify1 fm;;

let rec simplify fm =
  match fm with
    Not p -> simplify1 (Not(simplify p))
  | And(p,q) -> simplify1 (And(simplify p,simplify q))
  | Or(p,q) -> simplify1 (Or(simplify p,simplify q))
  | Imp(p,q) -> simplify1 (Imp(simplify p,simplify q))
  | Iff(p,q) -> simplify1 (Iff(simplify p,simplify q))
  | Forall(x,p) -> simplify1(Forall(x,simplify p))
  | Exists(x,p) -> simplify1(Exists(x,simplify p))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
simplify <<(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec nnf fm =
  match fm with
    And(p,q) -> And(nnf p,nnf q)
  | Or(p,q) -> Or(nnf p,nnf q)
  | Imp(p,q) -> Or(nnf(Not p),nnf q)
  | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
  | Not(Not p) -> nnf p
  | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
  | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
  | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
  | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
  | Forall(x,p) -> Forall(x,nnf p)
  | Exists(x,p) -> Exists(x,nnf p)
  | Not(Forall(x,p)) -> Exists(x,nnf(Not p))
  | Not(Exists(x,p)) -> Forall(x,nnf(Not p))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Example of NNF function in action.                                        *)
(* ------------------------------------------------------------------------- *)

(*
nnf <<(forall x. P(x))
      ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Prenex normal form.                                                       *)
(* ------------------------------------------------------------------------- *)

let rec pullquants fm =
  match fm with
    And(Forall(x,p),Forall(y,q)) ->
                          pullq(true,true) fm mk_forall mk_and x y p q
  | Or(Exists(x,p),Exists(y,q)) ->
                          pullq(true,true) fm mk_exists mk_or x y p q
  | And(Forall(x,p),q) -> pullq(true,false) fm mk_forall mk_and x x p q
  | And(p,Forall(y,q)) -> pullq(false,true) fm mk_forall mk_and y y p q
  | Or(Forall(x,p),q) ->  pullq(true,false) fm mk_forall mk_or x x p q
  | Or(p,Forall(y,q)) ->  pullq(false,true) fm mk_forall mk_or y y p q
  | And(Exists(x,p),q) -> pullq(true,false) fm mk_exists mk_and x x p q
  | And(p,Exists(y,q)) -> pullq(false,true) fm mk_exists mk_and y y p q
  | Or(Exists(x,p),q) ->  pullq(true,false) fm mk_exists mk_or x x p q
  | Or(p,Exists(y,q)) ->  pullq(false,true) fm mk_exists mk_or y y p q
  | _ -> fm

and pullq(l,r) fm quant op x y p q =
  let z = variant x (fv fm) in
  let p' = if l then subst (x |=> Var z) p else p
  and q' = if r then subst (y |=> Var z) q else q in
  quant z (pullquants(op p' q'));;

let rec prenex fm =
  match fm with
    Forall(x,p) -> Forall(x,prenex p)
  | Exists(x,p) -> Exists(x,prenex p)
  | And(p,q) -> pullquants(And(prenex p,prenex q))
  | Or(p,q) -> pullquants(Or(prenex p,prenex q))
  | _ -> fm;;

let pnf fm = prenex(nnf(simplify fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
pnf <<(forall x. P(x) \/ R(y))
      ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Get the functions in a term and formula.                                  *)
(* ------------------------------------------------------------------------- *)

let rec funcs tm =
  match tm with
    Var x -> []
  | Fn(f,args) -> itlist (union ** funcs) args [f,length args];;

let functions fm =
  atom_union (fun (R(p,a)) -> itlist (union ** funcs) a []) fm;;

(* ------------------------------------------------------------------------- *)
(* Core Skolemization function.                                              *)
(* ------------------------------------------------------------------------- *)

let rec skolem fm fns =
  match fm with
    Exists(y,p) ->
        let xs = fv(fm) in
        let f = variant (if xs = [] then "c_"^y else "f_"^y) fns in
        let fx = Fn(f,map (fun x -> Var x) xs) in
        skolem (subst (y |=> fx) p) (f::fns)
  | Forall(x,p) -> let p',fns' = skolem p fns in Forall(x,p'),fns'
  | And(p,q) -> skolem2 (fun (p,q) -> And(p,q)) (p,q) fns
  | Or(p,q) -> skolem2 (fun (p,q) -> Or(p,q)) (p,q) fns
  | _ -> fm,fns

and skolem2 cons (p,q) fns =
  let p',fns' = skolem p fns in
  let q',fns'' = skolem q fns' in
  cons(p',q'),fns'';;

(* ------------------------------------------------------------------------- *)
(* Overall Skolemization function.                                           *)
(* ------------------------------------------------------------------------- *)

let askolemize fm =
  fst(skolem (nnf(simplify fm)) (map fst (functions fm)));;

let rec specialize fm =
  match fm with
    Forall(x,p) -> specialize p
  | _ -> fm;;

let skolemize fm = specialize(pnf(askolemize fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
skolemize <<exists y. x < y ==> forall u. exists v. x * u < y * v>>;;

skolemize
 <<forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))>>;;
*)
(* ========================================================================= *)
(* Relation between FOL and propositonal logic; Herbrand theorem.            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Propositional valuation.                                                  *)
(* ------------------------------------------------------------------------- *)

let pholds d fm = eval fm (fun p -> d(Atom p));;

(* ------------------------------------------------------------------------- *)
(* Get the constants for Herbrand base, adding nullary one if necessary.     *)
(* ------------------------------------------------------------------------- *)

let herbfuns fm =
  let cns,fns = partition (fun (_,ar) -> ar = 0) (functions fm) in
  if cns = [] then ["c",0],fns else cns,fns;;

(* ------------------------------------------------------------------------- *)
(* Enumeration of ground terms and m-tuples, ordered by total fns.           *)
(* ------------------------------------------------------------------------- *)

let rec groundterms cntms funcs n =
  if n = 0 then cntms else
  itlist (fun (f,m) l -> map (fun args -> Fn(f,args))
                             (groundtuples cntms funcs (n - 1) m) @ l)
          funcs []

and groundtuples cntms funcs n m =
  if m = 0 then if n = 0 then [[]] else [] else
  itlist (fun k l -> allpairs (fun h t -> h::t)
                       (groundterms cntms funcs k)
                       (groundtuples cntms funcs (n - k) (m - 1)) @ l)
         (0 -- n) [];;

(* ------------------------------------------------------------------------- *)
(* Iterate modifier "mfn" over ground terms till "tfn" fails.                *)
(* ------------------------------------------------------------------------- *)

let rec herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples =
  print_string(string_of_int(length tried)^" ground instances tried; "^
               string_of_int(length fl)^" items in list");
  print_newline();
  match tuples with
    [] -> let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtups
  | tup::tups ->
          let fl' = mfn fl0 (subst(fpf fvs tup)) fl in
          if not(tfn fl') then tup::tried else
          herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup::tried) tups;;

(* ------------------------------------------------------------------------- *)
(* Hence a simple Gilmore-type procedure.                                    *)
(* ------------------------------------------------------------------------- *)

let gilmore_loop =
  let mfn djs0 ifn djs =
    filter (non trivial) (distrib (image (image ifn) djs0) djs) in
  herbloop mfn (fun djs -> djs <> []);;

let gilmore fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(gilmore_loop (simpdnf sfm) cntms funcs fvs 0 [[]] [] []);;

(* ------------------------------------------------------------------------- *)
(* First example and a little tracing.                                       *)
(* ------------------------------------------------------------------------- *)

(*
gilmore <<exists x. forall y. P(x) ==> P(y)>>;;

let sfm = skolemize(Not <<exists x. forall y. P(x) ==> P(y)>>);;

(* ------------------------------------------------------------------------- *)
(* Quick example.                                                            *)
(* ------------------------------------------------------------------------- *)

let p24 = gilmore
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;

(* ------------------------------------------------------------------------- *)
(* Slightly less easy example.                                               *)
(* ------------------------------------------------------------------------- *)

let p45 = gilmore
 <<(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))
              ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\
                      (forall y. G(y) /\ H(x,y) ==> J(x,y)))
   ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Apparently intractable example.                                           *)
(* ------------------------------------------------------------------------- *)

(**********

let p20 = gilmore
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

 **********)

(* ------------------------------------------------------------------------- *)
(* The Davis-Putnam procedure for first order logic.                         *)
(* ------------------------------------------------------------------------- *)

let dp_mfn cjs0 ifn cjs = union (image (image ifn) cjs0) cjs;;

let dp_loop = herbloop dp_mfn dpll;;

let davisputnam fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(dp_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []);;

(* ------------------------------------------------------------------------- *)
(* Show how much better than the Gilmore procedure this can be.              *)
(* ------------------------------------------------------------------------- *)

(*
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Try to cut out useless instantiations in final result.                    *)
(* ------------------------------------------------------------------------- *)

let rec dp_refine cjs0 fvs dunno need =
  match dunno with
    [] -> need
  | cl::dknow ->
      let mfn = dp_mfn cjs0 ** subst ** fpf fvs in
      let need' =
       if dpll(itlist mfn (need @ dknow) []) then cl::need else need in
      dp_refine cjs0 fvs dknow need';;

let dp_refine_loop cjs0 cntms funcs fvs n cjs tried tuples =
  let tups = dp_loop cjs0 cntms funcs fvs n cjs tried tuples in
  dp_refine cjs0 fvs tups [];;

(* ------------------------------------------------------------------------- *)
(* Show how few of the instances we really need. Hence unification!          *)
(* ------------------------------------------------------------------------- *)

let davisputnam' fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(dp_refine_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []);;

(*
let p36 = davisputnam'
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
                ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
   ==> (forall x. exists y. H(x,y))>>;;

let p29 = davisputnam'
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;
*)
(* ========================================================================= *)
(* Unification for first order terms.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec istriv env x t =
  match t with
    Var y -> y = x or defined env y & istriv env x (apply env y)
  | Fn(f,args) -> exists (istriv env x) args & failwith "cyclic";;

(* ------------------------------------------------------------------------- *)
(* Main unification procedure                                                *)
(* ------------------------------------------------------------------------- *)

let rec unify env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fargs),Fn(g,gargs))::oth ->
        if f = g & length fargs = length gargs
        then unify env (zip fargs gargs @ oth)
        else failwith "impossible unification"
  | (Var x,t)::oth | (t,Var x)::oth ->
        if defined env x then unify env ((apply env x,t)::oth)
        else unify (if istriv env x t then env else (x|->t) env) oth;;

(* ------------------------------------------------------------------------- *)
(* Solve to obtain a single instantiation.                                   *)
(* ------------------------------------------------------------------------- *)

let rec solve env =
  let env' = mapf (tsubst env) env in
  if env' = env then env else solve env';;

(* ------------------------------------------------------------------------- *)
(* Unification reaching a final solved form (often this isn't needed).       *)
(* ------------------------------------------------------------------------- *)

let fullunify eqs = solve (unify undefined eqs);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let unify_and_apply eqs =
  let i = fullunify eqs in
  let apply (t1,t2) = tsubst i t1,tsubst i t2 in
  map apply eqs;;

(*
unify_and_apply [<<|f(x,g(y))|>>,<<|f(f(z),w)|>>];;

unify_and_apply [<<|f(x,y)|>>,<<|f(y,x)|>>];;

(****  unify_and_apply [<<|f(x,g(y))|>>,<<|f(y,x)|>>];; *****)

unify_and_apply [<<|x_0|>>,<<|f(x_1,x_1)|>>;
                 <<|x_1|>>,<<|f(x_2,x_2)|>>;
                 <<|x_2|>>,<<|f(x_3,x_3)|>>];;
*)
(* ========================================================================= *)
(* Tableaux, seen as an optimized version of a Prawitz-like procedure.       *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unify literals (just pretend the toplevel relation is a function).        *)
(* ------------------------------------------------------------------------- *)

let rec unify_literals env tmp =
  match tmp with
    Atom(R(p1,a1)),Atom(R(p2,a2)) -> unify env [Fn(p1,a1),Fn(p2,a2)]
  | Not(p),Not(q) -> unify_literals env (p,q)
  | False,False -> env
  | _ -> failwith "Can't unify literals";;

(* ------------------------------------------------------------------------- *)
(* Unify complementary literals.                                             *)
(* ------------------------------------------------------------------------- *)

let unify_complements env (p,q) = unify_literals env (p,negate q);;

(* ------------------------------------------------------------------------- *)
(* Unify and refute a set of disjuncts.                                      *)
(* ------------------------------------------------------------------------- *)

let rec unify_refute djs env =
  match djs with
    [] -> env
  | d::odjs -> let pos,neg = partition positive d in
               tryfind (unify_refute odjs ** unify_complements env)
                       (allpairs (fun p q -> (p,q)) pos neg);;

(* ------------------------------------------------------------------------- *)
(* Hence a Prawitz-like procedure (using unification on DNF).                *)
(* ------------------------------------------------------------------------- *)

let rec prawitz_loop djs0 fvs djs n =
  let l = length fvs in
  let newvars = map (fun k -> "_"^string_of_int (n * l + k)) (1--l) in
  let inst = fpf fvs (map (fun x -> Var x) newvars) in
  let djs1 = distrib (image (image (subst inst)) djs0) djs in
  try unify_refute djs1 undefined,(n + 1)
  with Failure _ -> prawitz_loop djs0 fvs djs1 (n + 1);;

let prawitz fm =
  let fm0 = skolemize(Not(generalize fm)) in
  snd(prawitz_loop (simpdnf fm0) (fv fm0) [[]] 0);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let p20 = prawitz
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Comparison of number of ground instances.                                 *)
(* ------------------------------------------------------------------------- *)

let compare fm =
  prawitz fm,davisputnam fm;;

(*
let p19 = compare
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = compare
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p24 = compare
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;

let p39 = compare
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p42 = compare
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

(***** Too slow?

let p43 = compare
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

 ******)

let p44 = compare
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y)))
   ==> (exists x. J(x) /\ ~P(x))>>;;

let p59 = compare
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = compare
 <<forall x. P(x,f(x)) <=>
             exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

*)

(* ------------------------------------------------------------------------- *)
(* More standard tableau procedure, effectively doing DNF incrementally.     *)
(* ------------------------------------------------------------------------- *)

let rec tableau (fms,lits,n) cont (env,k) =
  if n < 0 then failwith "no proof at this level" else
  match fms with
    [] -> failwith "tableau: no proof"
  | And(p,q)::unexp ->
      tableau (p::q::unexp,lits,n) cont (env,k)
  | Or(p,q)::unexp ->
      tableau (p::unexp,lits,n) (tableau (q::unexp,lits,n) cont) (env,k)
  | Forall(x,p)::unexp ->
      let y = Var("_" ^ string_of_int k) in
      let p' = subst (x |=> y) p in
      tableau (p'::unexp@[Forall(x,p)],lits,n-1) cont (env,k+1)
  | fm::unexp ->
      try tryfind (fun l -> cont(unify_complements env (fm,l),k)) lits
      with Failure _ -> tableau (unexp,fm::lits,n) cont (env,k);;

let rec deepen f n =
  try print_string "Searching with depth limit ";
      print_int n; print_newline(); f n
  with Failure _ -> deepen f (n + 1);;

let tabrefute fms =
  deepen (fun n -> tableau (fms,[],n) (fun x -> x) (undefined,0); n) 0;;

let tab fm =
  let sfm = askolemize(Not(generalize fm)) in
  if sfm = False then 0 else tabrefute [sfm];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let p38 = tab
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Try to split up the initial formula first; often a big improvement.       *)
(* ------------------------------------------------------------------------- *)

let splittab fm = 
  map tabrefute (simpdnf(askolemize(Not(generalize fm))));;

(* ------------------------------------------------------------------------- *)
(* Example: the Andrews challenge.                                           *)
(* ------------------------------------------------------------------------- *)

(*
let p34 = splittab
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

(* ------------------------------------------------------------------------- *)
(* Another nice example from EWD 1602.                                       *)
(* ------------------------------------------------------------------------- *)

let ewd1062 = splittab
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Do all the equality-free Pelletier problems, and more, as examples.       *)
(* ------------------------------------------------------------------------- *)

(***********

let p1 = time splittab
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time splittab
 <<~ ~p <=> p>>;;

let p3 = time splittab
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time splittab
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time splittab
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time splittab
 <<p \/ ~p>>;;

let p7 = time splittab
 <<p \/ ~ ~ ~p>>;;

let p8 = time splittab
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time splittab
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time splittab
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time splittab
 <<p <=> p>>;;

let p12 = time splittab
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time splittab
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time splittab
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time splittab
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time splittab
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time splittab
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

(* ------------------------------------------------------------------------- *)
(* Pelletier problems: monadic predicate logic.                              *)
(* ------------------------------------------------------------------------- *)

let p18 = time splittab
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time splittab
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time splittab
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = time splittab
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time splittab
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time splittab
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time splittab
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time splittab
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
   ==> (exists x. Q(x) /\ P(x))>>;;

let p26 = time splittab
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
   ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time splittab
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x))
   ==> (forall x. V(x) ==> ~R(x))
       ==> (forall x. U(x) ==> ~V(x))>>;;

let p28 = time splittab
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time splittab
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time splittab
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
   ==> (forall x. U(x))>>;;

let p31 = time splittab
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\
   (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x))
   ==> (exists x. Q(x) /\ J(x))>>;;

let p32 = time splittab
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time splittab
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time splittab
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time splittab
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(* Full predicate logic (without identity and functions).                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time splittab
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time splittab
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time splittab
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time splittab
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time splittab
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time splittab
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time splittab
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

let p43 = time splittab
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

let p44 = time splittab
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

let p45 = time splittab
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let p46 = time splittab
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

(* ------------------------------------------------------------------------- *)
(* Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 *)
(* ------------------------------------------------------------------------- *)

let p55 = time splittab
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

let p57 = time splittab
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time splittab
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time splittab
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time splittab
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

(***** This is still too hard for us! Amazing...

let gilmore_1 = time splittab
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

 ******)

(*** This is not valid, according to Gilmore

let gilmore_2 = time splittab
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ***)

let gilmore_3 = time splittab
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time splittab
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time splittab
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time splittab
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time splittab
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time splittab
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_9 = time splittab
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
         ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
             (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time splittab
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

*************)
(* ========================================================================= *)
(* Resolution.                                                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Barber's paradox is an example of why we need factoring.                  *)
(* ------------------------------------------------------------------------- *)

let barb = <<~(exists b. forall x. shaves(b,x) <=> ~shaves(x,x))>>;;

(*
simpcnf(skolemize(Not barb));;
*)

(* ------------------------------------------------------------------------- *)
(* MGU of a set of literals.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec mgu l env =
  match l with
    a::b::rest -> mgu (b::rest) (unify_literals env (a,b))
  | _ -> solve env;;

let unifiable p q = can (unify_literals undefined) (p,q);;

(* ------------------------------------------------------------------------- *)
(* Rename a clause.                                                          *)
(* ------------------------------------------------------------------------- *)

let rename pfx cls =
  let fvs = fv(list_disj cls) in
  let vvs = map (fun s -> Var(pfx^s)) fvs  in
  map (subst(fpf fvs vvs)) cls;;

(* ------------------------------------------------------------------------- *)
(* General resolution rule, incorporating factoring as in Robinson's paper.  *)
(* ------------------------------------------------------------------------- *)

let resolvents cl1 cl2 p acc =
  let ps2 = filter (unifiable(negate p)) cl2 in
  if ps2 = [] then acc else
  let ps1 = filter (fun q -> q <> p & unifiable p q) cl1 in
  let pairs = allpairs (fun s1 s2 -> s1,s2)
                       (map (fun pl -> p::pl) (allsubsets ps1))
                       (allnonemptysubsets ps2) in
  itlist (fun (s1,s2) sof ->
           try image (subst (mgu (s1 @ map negate s2) undefined))
                     (union (subtract cl1 s1) (subtract cl2 s2)) :: sof
           with Failure _ -> sof) pairs acc;;

let resolve_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  itlist (resolvents cls1' cls2') cls1' [];;

(* ------------------------------------------------------------------------- *)
(* Basic "Argonne" loop.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true else resloop (used',ros@news);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example that works well.                                           *)
(* ------------------------------------------------------------------------- *)

(*
let davis_putnam_example = resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Matching of terms and literals.                                           *)
(* ------------------------------------------------------------------------- *)

let rec term_match env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fa),Fn(g,ga))::oth when f = g & length fa = length ga ->
        term_match env (zip fa ga @ oth)
  | (Var x,t)::oth ->
        if not (defined env x) then term_match ((x |-> t) env) oth
        else if apply env x = t then term_match env oth
        else failwith "term_match"
  | _ -> failwith "term_match";;

let rec match_literals env tmp =
  match tmp with
    Atom(R(p,a1)),Atom(R(q,a2)) | Not(Atom(R(p,a1))),Not(Atom(R(q,a2))) ->
       term_match env [Fn(p,a1),Fn(q,a2)]
  | _ -> failwith "match_literals";;

(* ------------------------------------------------------------------------- *)
(* Test for subsumption                                                      *)
(* ------------------------------------------------------------------------- *)

let subsumes_clause cls1 cls2 =
  let rec subsume env cls =
    match cls with
      [] -> env
    | l1::clt ->
        tryfind (fun l2 -> subsume (match_literals env (l1,l2)) clt)
                cls2 in
  can (subsume undefined) cls1;;

(* ------------------------------------------------------------------------- *)
(* With deletion of tautologies and bi-subsumption with "unused".            *)
(* ------------------------------------------------------------------------- *)

let rec replace cl lis =
  match lis with
    [] -> [cl]
  | c::cls -> if subsumes_clause cl c then cl::cls
              else c::(replace cl cls);;

let incorporate gcl cl unused =
  if trivial cl or
     exists (fun c -> subsumes_clause c cl) (gcl::unused)
  then unused else replace cl unused;;

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (resolve_clauses cl) used') [] in
      if mem [] news then true
      else resloop(used',itlist (incorporate cl) news ros);;

let pure_resolution fm = resloop([],simpcnf(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* This is now a lot quicker.                                                *)
(* ------------------------------------------------------------------------- *)

(*
let davis_putnam_example = resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Positive (P1) resolution.                                                 *)
(* ------------------------------------------------------------------------- *)

let presolve_clauses cls1 cls2 =
  if forall positive cls1 or forall positive cls2
  then resolve_clauses cls1 cls2 else [];;

let rec presloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cl::ros ->
      print_string(string_of_int(length used) ^ " used; "^
                   string_of_int(length unused) ^ " unused.");
      print_newline();
      let used' = insert cl used in
      let news = itlist(@) (mapfilter (presolve_clauses cl) used') [] in
      if mem [] news then true else
      presloop(used',itlist (incorporate cl) news ros);;

let pure_presolution fm = presloop([],simpcnf(specialize(pnf fm)));;

let presolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_presolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example: the (in)famous Los problem.                                      *)
(* ------------------------------------------------------------------------- *)

(*
let los = time presolution
 <<(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(* Introduce a set-of-support restriction.                                   *)
(* ------------------------------------------------------------------------- *)

let pure_resolution fm =
  resloop(partition (exists positive) (simpcnf(specialize(pnf fm))));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* The Pelletier examples again.                                             *)
(* ------------------------------------------------------------------------- *)

(***********

let p1 = time presolution
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time presolution
 <<~ ~p <=> p>>;;

let p3 = time presolution
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time presolution
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time presolution
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time presolution
 <<p \/ ~p>>;;

let p7 = time presolution
 <<p \/ ~ ~ ~p>>;;

let p8 = time presolution
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time presolution
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time presolution
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time presolution
 <<p <=> p>>;;

let p12 = time presolution
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time presolution
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time presolution
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time presolution
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time presolution
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time presolution
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time presolution
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time presolution
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time presolution
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = time presolution
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time presolution
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time presolution
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time presolution
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time presolution
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time presolution
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time presolution
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. V(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time presolution
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time presolution
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time presolution
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time presolution
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time presolution
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time presolution
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time presolution
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time presolution
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time presolution
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time presolution
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

(*** This one seems too slow

let p38 = time presolution
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

 ***)

let p39 = time presolution
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time presolution
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time presolution
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

(*** Also very slow

let p42 = time presolution
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

 ***)

(*** and this one too..

let p43 = time presolution
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

 ***)

let p44 = time presolution
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

(*** and this...

let p45 = time presolution
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

 ***)

(*** and this

let p46 = time presolution
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time presolution
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

let p57 = time presolution
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time presolution
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time presolution
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time presolution
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time presolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

(*** This is not valid, according to Gilmore

let gilmore_2 = time presolution
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ***)

let gilmore_3 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time presolution
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time presolution
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time presolution
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time presolution
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

(*** This one still isn't easy!

let gilmore_9 = time presolution
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time presolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

************)
*)

(* ------------------------------------------------------------------------- *)
(* Example                                                                   *)
(* ------------------------------------------------------------------------- *)

(*
let gilmore_1 = resolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

(* ------------------------------------------------------------------------- *)
(* Pelletiers yet again.                                                     *)
(* ------------------------------------------------------------------------- *)

(************

let p1 = time resolution
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time resolution
 <<~ ~p <=> p>>;;

let p3 = time resolution
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time resolution
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time resolution
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time resolution
 <<p \/ ~p>>;;

let p7 = time resolution
 <<p \/ ~ ~ ~p>>;;

let p8 = time resolution
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time resolution
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time resolution
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time resolution
 <<p <=> p>>;;

let p12 = time resolution
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time resolution
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time resolution
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time resolution
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time resolution
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time resolution
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time resolution
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time resolution
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time resolution
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time resolution
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))>>;;

let p22 = time resolution
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time resolution
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time resolution
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time resolution
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time resolution
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time resolution
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. V(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time resolution
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time resolution
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time resolution
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time resolution
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time resolution
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time resolution
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time resolution
 <<((exists x. forall y. P(x) <=> P(y)) <=>
   ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
  ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time resolution
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time resolution
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time resolution
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

(*** This one seems too slow

let p38 = time resolution
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

 ***)

let p39 = time resolution
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time resolution
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time resolution
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

(*** Also very slow

let p42 = time resolution
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

 ***)

(*** and this one too..

let p43 = time resolution
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

 ***)

let p44 = time resolution
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

(*** and this...

let p45 = time resolution
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

 ***)

(*** and this

let p46 = time resolution
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time resolution
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

let p57 = time resolution
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time resolution
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time resolution
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time resolution
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time resolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

(*** This is not valid, according to Gilmore

let gilmore_2 = time resolution
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ***)

let gilmore_3 = time resolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time resolution
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time resolution
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time resolution
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time resolution
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time resolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

(*** This one still isn't easy!

let gilmore_9 = time resolution
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The (in)famous Los problem.                                               *)
(* ------------------------------------------------------------------------- *)

let los = time resolution
 <<(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;

**************)
*)
(* ========================================================================= *)
(* Backchaining procedure for Horn clauses, and toy Prolog implementation.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rename a rule.                                                            *)
(* ------------------------------------------------------------------------- *)

let renamerule k (asm,c) =
  let fvs = fv(list_conj(c::asm)) in
  let n = length fvs in
  let vvs = map (fun i -> "_" ^ string_of_int i) (k -- (k+n-1)) in
  let inst = subst(fpf fvs (map (fun x -> Var x) vvs)) in
  (map inst asm,inst c),k+n;;

(* ------------------------------------------------------------------------- *)
(* Basic prover for Horn clauses based on backchaining with unification.     *)
(* ------------------------------------------------------------------------- *)

let rec backchain rules n k env goals =
  match goals with
    [] -> env
  | g::gs ->
     if n = 0 then failwith "Too deep" else
     tryfind (fun rule ->
        let (a,c),k' = renamerule k rule in
        backchain rules (n - 1) k' (unify_literals env (c,g)) (a @ gs))
     rules;;

let hornify cls =
  let pos,neg = partition positive cls in
  if length pos > 1 then failwith "non-Horn clause"
  else (map negate neg,if pos = [] then False else hd pos);;

let hornprove fm =
  let rules = map hornify (simpcnf(skolemize(Not(generalize fm)))) in
  deepen (fun n -> backchain rules n 0 undefined [False],n) 0;;

(* ------------------------------------------------------------------------- *)
(* A Horn example.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
let p32 = hornprove
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

(* ------------------------------------------------------------------------- *)
(* A non-Horn example.                                                       *)
(* ------------------------------------------------------------------------- *)

(****************

hornprove <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

**********)
*)

(* ------------------------------------------------------------------------- *)
(* Parsing rules in a Prolog-like syntax.                                    *)
(* ------------------------------------------------------------------------- *)

let parserule s =
  let c,rest =
    parse_formula (parse_infix_atom,parse_atom) [] (lex(explode s)) in
  let asm,rest1 =
    if rest <> [] & hd rest = ":-"
    then parse_list ","
          (parse_formula (parse_infix_atom,parse_atom) []) (tl rest)
    else [],rest in
  if rest1 = [] then (asm,c) else failwith "Extra material after rule";;

(* ------------------------------------------------------------------------- *)
(* Prolog interpreter: just use depth-first search not iterative deepening.  *)
(* ------------------------------------------------------------------------- *)

let simpleprolog rules gl =
  backchain (map parserule rules) (-1) 0 undefined [parse gl];;

(* ------------------------------------------------------------------------- *)
(* Ordering example.                                                         *)
(* ------------------------------------------------------------------------- *)

(*
let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"];;

simpleprolog lerules "S(S(0)) <= S(S(S(0)))";;

(*** simpleprolog lerules "S(S(0)) <= S(0)";;
 ***)

let env = simpleprolog lerules "S(S(0)) <= X";;
apply env "X";;
*)

(* ------------------------------------------------------------------------- *)
(* With instantiation collection to produce a more readable result.          *)
(* ------------------------------------------------------------------------- *)

let prolog rules gl =
  let i = solve(simpleprolog rules gl) in
  mapfilter (fun x -> Atom(R("=",[Var x; apply i x]))) (fv(parse gl));;

(* ------------------------------------------------------------------------- *)
(* Example again.                                                            *)
(* ------------------------------------------------------------------------- *)

(*
prolog lerules "S(S(0)) <= X";;

(* ------------------------------------------------------------------------- *)
(* Append example, showing symmetry between inputs and outputs.              *)
(* ------------------------------------------------------------------------- *)

let appendrules =
  ["append(nil,L,L)"; "append(H::T,L,H::A) :- append(T,L,A)"];;

prolog appendrules "append(1::2::nil,3::4::nil,Z)";;

prolog appendrules "append(1::2::nil,Y,1::2::3::4::nil)";;

prolog appendrules "append(X,3::4::nil,1::2::3::4::nil)";;

prolog appendrules "append(X,Y,1::2::3::4::nil)";;

(* ------------------------------------------------------------------------- *)
(* However this way round doesn't work.                                      *)
(* ------------------------------------------------------------------------- *)

(***
 *** prolog appendrules "append(X,3::4::nil,X)";;
 ***)

(* ------------------------------------------------------------------------- *)
(* A sorting example (from Lloyd's "Foundations of Logic Programming").      *)
(* ------------------------------------------------------------------------- *)

let sortrules =
 ["sort(X,Y) :- perm(X,Y),sorted(Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

prolog sortrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

(* ------------------------------------------------------------------------- *)
(* Yet with a simple swap of the first two predicates...                     *)
(* ------------------------------------------------------------------------- *)

let badrules =
 ["sort(X,Y) :- sorted(Y), perm(X,Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

(*** This no longer works

prolog badrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

 ***)
*)                           
(* ========================================================================= *)
(* Model elimination procedure (MESON version, based on Stickel's PTTP).     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Example of naivety of tableau prover.                                     *)
(* ------------------------------------------------------------------------- *)

(*
tab <<forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))>>;;

tab <<forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The interesting example where tableaux connections make the proof longer. *)
(* Unfortuntely this gets hammered by normalization first...                 *)
(* ------------------------------------------------------------------------- *)

tab <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
      (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
      (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Generation of contrapositives.                                            *)
(* ------------------------------------------------------------------------- *)

let contrapositives cls =
  let base = map (fun c -> map negate (subtract cls [c]),c) cls in
  if forall negative cls then (map negate cls,False)::base else base;;

(* ------------------------------------------------------------------------- *)
(* The core of MESON: ancestor unification or Prolog-style extension.        *)
(* ------------------------------------------------------------------------- *)

let rec mexpand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun rule -> let (asm,c),k' = renamerule k rule in
                 itlist (mexpand rules (g::ancestors)) asm cont
                        (unify_literals env (g,c),n-length asm,k'))
    rules;;

(* ------------------------------------------------------------------------- *)
(* Full MESON procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

let puremeson fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let davis_putnam_example = meson
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* With repetition checking and divide-and-conquer search.                   *)
(* ------------------------------------------------------------------------- *)

let rec equal env fm1 fm2 =
  try unify_literals env (fm1,fm2) == env with Failure _ -> false;;

let expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
   expfn goals1 (fun (e1,r1,k1) ->
        expfn goals2 (fun (e2,r2,k2) ->
                        if n2 + r1 <= n3 + r2 then failwith "pair"
                        else cont(e2,r2,k2))
              (e1,n2+r1,k1))
        (env,n1,k);;

let rec mexpand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep"
  else if exists (equal env g) ancestors then failwith "repetition" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun r -> let (asm,c),k' = renamerule k r in
              mexpands rules (g::ancestors) asm cont
                       (unify_literals env (g,c),n-length asm,k'))
    rules

and mexpands rules ancestors gs cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  let m = length gs in
  if m <= 1 then itlist (mexpand rules ancestors) gs cont (env,n,k) else
  let n1 = n / 2 in
  let n2 = n - n1 in
  let goals1,goals2 = chop_list (m / 2) gs in
  let expfn = expand2 (mexpands rules ancestors) in
  try expfn goals1 n1 goals2 n2 (-1) cont env k
  with Failure _ -> expfn goals2 n1 goals1 n2 n1 cont env k;;

let puremeson fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* The Los problem (depth 20) and the Steamroller (depth 53) --- lengthier.  *)
(* ------------------------------------------------------------------------- *)

(*
(***********

let los = meson
 <<(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;

let steamroller = meson
 <<((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\
   ((forall x. P2(x) ==> P0(x)) /\ (exists x. P2(x))) /\
   ((forall x. P3(x) ==> P0(x)) /\ (exists x. P3(x))) /\
   ((forall x. P4(x) ==> P0(x)) /\ (exists x. P4(x))) /\
   ((forall x. P5(x) ==> P0(x)) /\ (exists x. P5(x))) /\
   ((exists x. Q1(x)) /\ (forall x. Q1(x) ==> Q0(x))) /\
   (forall x. P0(x)
              ==> (forall y. Q0(y) ==> R(x,y)) \/
                  ((forall y. P0(y) /\ S0(y,x) /\
                              (exists z. Q0(z) /\ R(y,z))
                              ==> R(x,y)))) /\
   (forall x y. P3(y) /\ (P5(x) \/ P4(x)) ==> S0(x,y)) /\
   (forall x y. P3(x) /\ P2(y) ==> S0(x,y)) /\
   (forall x y. P2(x) /\ P1(y) ==> S0(x,y)) /\
   (forall x y. P1(x) /\ (P2(y) \/ Q1(y)) ==> ~(R(x,y))) /\
   (forall x y. P3(x) /\ P4(y) ==> R(x,y)) /\
   (forall x y. P3(x) /\ P5(y) ==> ~(R(x,y))) /\
   (forall x. (P4(x) \/ P5(x)) ==> exists y. Q0(y) /\ R(x,y))
   ==> exists x y. P0(x) /\ P0(y) /\
                   exists z. Q1(z) /\ R(y,z) /\ R(x,y)>>;;

****************)


(* ------------------------------------------------------------------------- *)
(* Test it.                                                                  *)
(* ------------------------------------------------------------------------- *)

let prop_1 = time meson
 <<p ==> q <=> ~q ==> ~p>>;;

let prop_2 = time meson
 <<~ ~p <=> p>>;;

let prop_3 = time meson
 <<~(p ==> q) ==> q ==> p>>;;

let prop_4 = time meson
 <<~p ==> q <=> ~q ==> p>>;;

let prop_5 = time meson
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let prop_6 = time meson
 <<p \/ ~p>>;;

let prop_7 = time meson
 <<p \/ ~ ~ ~p>>;;

let prop_8 = time meson
 <<((p ==> q) ==> p) ==> p>>;;

let prop_9 = time meson
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let prop_10 = time meson
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let prop_11 = time meson
 <<p <=> p>>;;

let prop_12 = time meson
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let prop_13 = time meson
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let prop_14 = time meson
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let prop_15 = time meson
 <<p ==> q <=> ~p \/ q>>;;

let prop_16 = time meson
 <<(p ==> q) \/ (q ==> p)>>;;

let prop_17 = time meson
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time meson
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time meson
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time meson
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time meson
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time meson
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time meson
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time meson
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time meson
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time meson
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time meson
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. V(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time meson
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time meson
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time meson
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time meson
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time meson
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time meson
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time meson
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time meson
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time meson
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time meson
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time meson
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time meson
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time meson
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time meson
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time meson
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

let p43 = time meson
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

let p44 = time meson
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

let p45 = time meson
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let p46 = time meson
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time meson
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

let p57 = time meson
 <<P(f((a),b),f(b,c)) /\
  P(f(b,c),f(a,c)) /\
  (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
  ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time meson
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time meson
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time meson
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

(*** Amazingly, this still seems non-trivial... in HOL it works at depth 45!

let gilmore_1 = time meson
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

 ***)

(*** This is not valid, according to Gilmore

let gilmore_2 = time meson
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ***)

let gilmore_3 = time meson
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time meson
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time meson
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time meson
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time meson
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time meson
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

(*** This is still a very hard problem

let gilmore_9 = time meson
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Translation of Gilmore procedure using separate definitions.              *)
(* ------------------------------------------------------------------------- *)

let gilmore_9a = time meson
 <<(forall x y. P(x,y) <=>
                forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
   ==> forall x. exists y. forall z.
             (P(y,x) ==> (P(x,z) ==> P(x,y))) /\
             (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time meson
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The "connections make things worse" example once again.                   *)
(* ------------------------------------------------------------------------- *)

meson <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
        (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
*)
(* ========================================================================= *)
(* Illustration of Skolemizing a set of formulas                             *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec rename_term tm =
  match tm with
    Fn(f,args) -> Fn("old_"^f,map rename_term args)
  | _ -> tm;;

let rename_form = onformula rename_term;;

let rec skolems fms corr =
  match fms with
    [] -> [],corr
  | (p::ofms) ->
        let p',corr' = skolem (rename_form p) corr in
        let ps',corr'' = skolems ofms corr' in
        p'::ps',corr'';;

let skolemizes fms = fst(skolems fms []);;

(*
skolemizes [<<exists x y. x + y = 2>>;
            <<forall x. exists y. x + 1 = y>>];;
*)
(* ========================================================================= *)
(* First order logic with equality.                                          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let is_eq = function (Atom(R("=",_))) -> true | _ -> false;;

let mk_eq s t = Atom(R("=",[s;t]));;

let dest_eq fm =
  match fm with
    Atom(R("=",[s;t])) -> s,t
  | _ -> failwith "dest_eq: not an equation";;

let lhs eq = fst(dest_eq eq) and rhs eq = snd(dest_eq eq);;

(* ------------------------------------------------------------------------- *)
(* The set of predicates in a formula.                                       *)
(* ------------------------------------------------------------------------- *)

let rec predicates fm = atom_union (fun (R(p,a)) -> [p,length a]) fm;;

(* ------------------------------------------------------------------------- *)
(* Code to generate equality axioms for functions.                           *)
(* ------------------------------------------------------------------------- *)

let function_congruence (f,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let ant = end_itlist mk_and (map2 mk_eq args_x args_y)
  and con = mk_eq (Fn(f,args_x)) (Fn(f,args_y)) in
  [itlist mk_forall (argnames_x @ argnames_y) (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
function_congruence ("f",3);;

function_congruence ("+",2);;
*)

(* ------------------------------------------------------------------------- *)
(* And for predicates.                                                       *)
(* ------------------------------------------------------------------------- *)

let predicate_congruence (p,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let ant = end_itlist mk_and (map2 mk_eq args_x args_y)
  and con = Imp(Atom(R(p,args_x)),Atom(R(p,args_y))) in
  [itlist mk_forall (argnames_x @ argnames_y) (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Hence implement logic with equality just by adding equality "axioms".     *)
(* ------------------------------------------------------------------------- *)

let equivalence_axioms =
  [<<forall x. x = x>>; <<forall x y z. x = y /\ x = z ==> y = z>>];;

let equalitize fm =
  let allpreds = predicates fm in
  if not (mem ("=",2) allpreds) then fm else
  let preds = subtract allpreds ["=",2] and funcs = functions fm in
  let axioms = itlist (union ** function_congruence) funcs
                      (itlist (union ** predicate_congruence) preds
                              equivalence_axioms) in
  Imp(end_itlist mk_and axioms,fm);;

(* ------------------------------------------------------------------------- *)
(* A simple example (see EWD1266a and the application to Morley's theorem).  *)
(* ------------------------------------------------------------------------- *)

(*
let ewd = equalitize
 <<(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)>>;;

meson ewd;;

(* ------------------------------------------------------------------------- *)
(* Wishnu Prasetya's example (even nicer with an "exists unique" primitive). *)
(* ------------------------------------------------------------------------- *)

let wishnu = equalitize
 <<(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')>>;;

time meson wishnu;;

(* ------------------------------------------------------------------------- *)
(* More challenging equational problems. (Size 18, 61814 seconds.)           *)
(* ------------------------------------------------------------------------- *)

(*********

(meson ** equalitize)
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. 1 * x = x) /\
   (forall x. i(x) * x = 1)
   ==> forall x. x * i(x) = 1>>;;

 ********)

(* ------------------------------------------------------------------------- *)
(* Other variants not mentioned in book.                                     *)
(* ------------------------------------------------------------------------- *)

(*************

(meson ** equalitize)
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. 1 * x = x) /\
   (forall x. x * 1 = x) /\
   (forall x. x * x = 1)
   ==> forall x y. x * y  = y * x>>;;

(* ------------------------------------------------------------------------- *)
(* With symmetry at leaves and one-sided congruences (Size = 16, 54659 s).   *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x. x = x) /\
   (forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x y z. =((x * y) * z,x * (y * z))) /\
   (forall x. 1 * x = x) /\
   (forall x. x = 1 * x) /\
   (forall x. i(x) * x = 1) /\
   (forall x. 1 = i(x) * x) /\
   (forall x y. x = y ==> i(x) = i(y)) /\
   (forall x y z. x = y ==> x * z = y * z) /\
   (forall x y z. x = y ==> z * x = z * y) /\
   (forall x y z. x = y /\ y = z ==> x = z)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

(* ------------------------------------------------------------------------- *)
(* Newer version of stratified equalities.                                   *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
   (forall x. axiom(1 * x,x)) /\
   (forall x. axiom(x,1 * x)) /\
   (forall x. axiom(i(x) * x,1)) /\
   (forall x. axiom(1,i(x) * x)) /\
   (forall x x'. x = x' ==> cchain(i(x),i(x'))) /\
   (forall x x' y y'. x = x' /\ y = y' ==> cchain(x * y,x' * y'))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall x x' u. x = x' /\ achain(i(x'),u) ==> cchain(i(x),u)) /\
   (forall x x' y y' u.
        x = x' /\ y = y' /\ achain(x' * y',u) ==> cchain(x * y,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

let fm =
 <<(forall x y z. axiom(x * (y * z),(x * y) * z)) /\
   (forall x y z. axiom((x * y) * z,x * (y * z)) /\
   (forall x. axiom(1 * x,x)) /\
   (forall x. axiom(x,1 * x)) /\
   (forall x. axiom(i(x) * x,1)) /\
   (forall x. axiom(1,i(x) * x)) /\
   (forall x x'. x = x' ==> cong(i(x),i(x'))) /\
   (forall x x' y y'. x = x' /\ y = y' ==> cong(x * y,x' * y'))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t. cong(s,t) ==> cchain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t)
   ==> forall x. x * i(x) = 1>>;;

time meson fm;;

(* ------------------------------------------------------------------------- *)
(* Showing congruence closure.                                               *)
(* ------------------------------------------------------------------------- *)

let fm = equalitize
 <<forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c>>;;

time meson fm;;

let fm =
 <<axiom(f(f(f(f(f(c))))),c) /\
   axiom(c,f(f(f(f(f(c)))))) /\
   axiom(f(f(f(c))),c) /\
   axiom(c,f(f(f(c)))) /\
   (forall s t. axiom(s,t) ==> achain(s,t)) /\
   (forall s t. cong(s,t) ==> cchain(s,t)) /\
   (forall s t u. axiom(s,t) /\ (t = u) ==> achain(s,u)) /\
   (forall s t u. cong(s,t) /\ achain(t,u) ==> cchain(s,u)) /\
   (forall s t. cchain(s,t) ==> s = t) /\
   (forall s t. achain(s,t) ==> s = t) /\
   (forall t. t = t) /\
   (forall x y. x = y ==> cong(f(x),f(y)))
   ==> f(c) = c>>;;

time meson fm;;

(* ------------------------------------------------------------------------- *)
(* With stratified equalities.                                               *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
   (forall x y z. eqA ((x * y) * z)) /\
   (forall x. eqA (1 * x,x)) /\
   (forall x. eqA (x,1 * x)) /\
   (forall x. eqA (i(x) * x,1)) /\
   (forall x. eqA (1,i(x) * x)) /\
   (forall x. eqA (x,x)) /\
   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqT (x,y) ==> eqC (i(x),i(y))) /\
   (forall w x y z. eqA (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqA (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqA (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqC (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqA (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqC (y,z) ==> eqC (w * y,x * z)) /\
   (forall w x y z. eqT (w,x) /\ eqT (y,z) ==> eqC (w * y,x * z)) /\
   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
   ==> forall x. eqT (x * i(x),1)>>;;

(* ------------------------------------------------------------------------- *)
(* With transitivity chains...                                               *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x y z. eqA (x * (y * z),(x * y) * z)) /\
   (forall x y z. eqA ((x * y) * z)) /\
   (forall x. eqA (1 * x,x)) /\
   (forall x. eqA (x,1 * x)) /\
   (forall x. eqA (i(x) * x,1)) /\
   (forall x. eqA (1,i(x) * x)) /\
   (forall x y. eqA (x,y) ==> eqC (i(x),i(y))) /\
   (forall x y. eqC (x,y) ==> eqC (i(x),i(y))) /\
   (forall w x y. eqA (w,x) ==> eqC (w * y,x * y)) /\
   (forall w x y. eqC (w,x) ==> eqC (w * y,x * y)) /\
   (forall x y z. eqA (y,z) ==> eqC (x * y,x * z)) /\
   (forall x y z. eqC (y,z) ==> eqC (x * y,x * z)) /\
   (forall x y z. eqA (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqA (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqC (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqA (x,y) /\ eqT (y,z) ==> eqT (x,z)) /\
   (forall x y z. eqC (x,y) /\ eqT (y,z) ==> eqT (x,z))
   ==> forall x. eqT (x * i(x),1) \/ eqC (x * i(x),1)>>;;

time meson fm;;

(* ------------------------------------------------------------------------- *)
(* Enforce canonicity (proof size = 20).                                     *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x y z. eq1(x * (y * z),(x * y) * z)) /\
   (forall x y z. eq1((x * y) * z,x * (y * z))) /\
   (forall x. eq1(1 * x,x)) /\
   (forall x. eq1(x,1 * x)) /\
   (forall x. eq1(i(x) * x,1)) /\
   (forall x. eq1(1,i(x) * x)) /\
   (forall x y z. eq1(x,y) ==> eq1(x * z,y * z)) /\
   (forall x y z. eq1(x,y) ==> eq1(z * x,z * y)) /\
   (forall x y z. eq1(x,y) /\ eq2(y,z) ==> eq2(x,z)) /\
   (forall x y. eq1(x,y) ==> eq2(x,y))
   ==> forall x. eq2(x,i(x))>>;;

time meson fm;;

******************)
*)
(* ========================================================================= *)
(* Simple congruence closure.                                                *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec subterms tm =
  match tm with
    Fn(f,args) -> itlist (union ** subterms) args [tm]
  | _ -> [tm];;

(* ------------------------------------------------------------------------- *)
(* Test whether subterms are congruent under an equivalence.                 *)
(* ------------------------------------------------------------------------- *)

let congruent eqv (s,t) =
  match (s,t) with
    Fn(f,a1),Fn(g,a2) -> f = g & forall2 (equivalent eqv) a1 a2
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Merging of terms, with congruence closure.                                *)
(* ------------------------------------------------------------------------- *)

let rec emerge (s,t) (eqv,pfn) =
  let s' = canonize eqv s and t' = canonize eqv t in
  if s' = t' then (eqv,pfn) else
  let sp = tryapplyl pfn s' and tp = tryapplyl pfn t' in
  let eqv' = equate (s,t) eqv in
  let st' = canonize eqv' s' in
  let pfn' = (st' |-> union sp tp) pfn in
  itlist (fun (u,v) (eqv,pfn) ->
                if congruent eqv (u,v) then emerge (u,v) (eqv,pfn)
                else eqv,pfn)
         (allpairs (fun u v -> (u,v)) sp tp) (eqv',pfn');;

(* ------------------------------------------------------------------------- *)
(* Satisfiability of conjunction of ground equations and inequations.        *)
(* ------------------------------------------------------------------------- *)

let predecessors t pfn =
  match t with
    Fn(f,a) -> itlist (fun s f -> (s |-> insert t (tryapplyl f s)) f)
                      (setify a) pfn
  | _ -> pfn;;

let ccsatisfiable fms =
  let pos,neg = partition positive fms in
  let eqps = map dest_eq pos and eqns = map (dest_eq ** negate) neg in
  let lrs = map fst eqps @ map snd eqps @ map fst eqns @ map snd eqns in
  let pfn = itlist predecessors (unions(map subterms lrs)) undefined in
  let eqv,_ = itlist emerge eqps (unequal,pfn) in
  forall (fun (l,r) -> not(equivalent eqv l r)) eqns;;

(* ------------------------------------------------------------------------- *)
(* Validity checking a universal formula.                                    *)
(* ------------------------------------------------------------------------- *)

let ccvalid fm =
  let fms = simpdnf(askolemize(Not(generalize fm))) in
  not (exists ccsatisfiable fms);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
ccvalid <<f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c
          ==> f(c) = c \/ f(g(c)) = g(f(c))>>;;

ccvalid <<f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c>>;;

(* ------------------------------------------------------------------------- *)
(* For debugging. Maybe I will incorporate into a prettyprinter one day.     *)
(* ------------------------------------------------------------------------- *)

(**********

let showequiv ptn =
  let fn = reverseq (equated ptn) ptn in
  map (apply fn) (dom fn);;

 **********)

*)
(* ========================================================================= *)
(* Rewriting.                                                                *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rewriting at the top level with first of list of equations.               *)
(* ------------------------------------------------------------------------- *)

let rec rewrite1 eqs t =
  match eqs with
    Atom(R("=",[l;r]))::oeqs ->
     (try tsubst (term_match undefined [l,t]) r
      with Failure _ -> rewrite1 oeqs t)
  | _ -> failwith "rewrite1";;

(* ------------------------------------------------------------------------- *)
(* Rewriting repeatedly and at depth (top-down).                             *)
(* ------------------------------------------------------------------------- *)

let rec rewrite eqs tm =
  try rewrite eqs (rewrite1 eqs tm) with Failure _ ->
  match tm with
    Var x -> tm
  | Fn(f,args) -> let tm' = Fn(f,map (rewrite eqs) args) in
                  if tm' = tm then tm else rewrite eqs tm';;

(* ------------------------------------------------------------------------- *)
(* Example: 3 * 2 + 4 in successor notation.                                 *)
(* ------------------------------------------------------------------------- *)

(*
rewrite [<<0 + x = x>>; <<S(x) + y = S(x + y)>>;
         <<0 * x = 0>>; <<S(x) * y = y + x * y>>]
        <<|S(S(S(0))) * S(S(0)) + S(S(S(S(0))))|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Note that ML doesn't accept nonlinear patterns.                           *)
(* ------------------------------------------------------------------------- *)

(*********** Point being that CAML doesn't accept nonlinear patterns

function (x,x) -> 0;;

 *********** Actually fun x x -> 0 works, but the xs seem to be
 *********** considered distinct
 **********)
(* ========================================================================= *)
(* Term orderings.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec termsize tm =
  match tm with
    Var x -> 1
  | Fn(f,args) -> itlist (fun t n -> termsize t + n) args 1;;

(* ------------------------------------------------------------------------- *)
(* This fails the rewrite properties.                                        *)
(* ------------------------------------------------------------------------- *)

(*
let s = <<|f(x,x,x)|>> and t = <<|g(x,y)|>>;;

termsize s > termsize t;;

let i = ("y" |=> <<|f(x,x,x)|>>);;

termsize (tsubst i s) > termsize (tsubst i t);;
*)

(* ------------------------------------------------------------------------- *)
(* Lexicographic path order.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 & lexord ord t1 t2
  | _ -> false;;

let rec lpo_gt w s t =
  match (s,t) with
    (_,Var x) ->
        not(s = t) & mem x (fvt s)
  | (Fn(f,fargs),Fn(g,gargs)) ->
        exists (fun si -> lpo_ge w si t) fargs or
        forall (lpo_gt w s) gargs &
        (f = g & lexord (lpo_gt w) fargs gargs or
         w (f,length fargs) (g,length gargs))
  | _ -> false

and lpo_ge w s t = (s = t) or lpo_gt w s t;;

(* ------------------------------------------------------------------------- *)
(* More convenient way of specifying weightings.                             *)
(* ------------------------------------------------------------------------- *)

let weight lis (f,n) (g,m) = if f = g then n > m else earlier lis g f;;
(* ========================================================================= *)
(* Knuth-Bendix completion.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let renamepair (fm1,fm2) =
  let fvs1 = fv fm1 and fvs2 = fv fm2 in
  let nms1,nms2 = chop_list(length fvs1)
                           (map (fun n -> Var("x"^string_of_int n))
                                (0--(length fvs1 + length fvs2 - 1))) in
  subst (fpf fvs1 nms1) fm1,subst (fpf fvs2 nms2) fm2;;

(* ------------------------------------------------------------------------- *)
(* Rewrite (using unification) with l = r inside tm to give a critical pair. *)
(* ------------------------------------------------------------------------- *)

let rec listcases fn rfn lis acc =
  match lis with
    [] -> acc
  | h::t -> fn h (fun i h' -> rfn i (h'::t)) @
            listcases fn (fun i t' -> rfn i (h::t')) t acc;;

let rec overlaps (l,r) tm rfn =
  match tm with
    Fn(f,args) ->
        listcases (overlaps (l,r)) (fun i a -> rfn i (Fn(f,a))) args
                  (try [rfn (fullunify [l,tm]) r] with Failure _ -> [])
  | Var x -> [];;

(* ------------------------------------------------------------------------- *)
(* Generate all critical pairs between two equations.                        *)
(* ------------------------------------------------------------------------- *)

let crit1 (Atom(R("=",[l1;r1]))) (Atom(R("=",[l2;r2]))) =
  overlaps (l1,r1) l2 (fun i t -> subst i (mk_eq t r2));;

let critical_pairs fma fmb =
  let fm1,fm2 = renamepair (fma,fmb) in
  if fma = fmb then crit1 fm1 fm2
  else union (crit1 fm1 fm2) (crit1 fm2 fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
let eq = <<f(f(x)) = g(x)>> in critical_pairs eq eq;;
*)

(* ------------------------------------------------------------------------- *)
(* Orienting an equation.                                                    *)
(* ------------------------------------------------------------------------- *)

let normalize_and_orient ord eqs (Atom(R("=",[s;t]))) =
  let s' = rewrite eqs s and t' = rewrite eqs t in
  if ord s' t' then (s',t') else if ord t' s' then (t',s')
  else failwith "Can't orient equation";;

(* ------------------------------------------------------------------------- *)
(* Status report so the user doesn't get too bored.                          *)
(* ------------------------------------------------------------------------- *)

let status(eqs,def,crs) eqs0 =
  if eqs = eqs0 & (length crs) mod 1000 <> 0 then () else
  (print_string(string_of_int(length eqs)^" equations and "^
                string_of_int(length crs)^" pending critical pairs + "^
                string_of_int(length def)^" deferred");
   print_newline());;

(* ------------------------------------------------------------------------- *)
(* Completion main loop (deferring non-orientable equations).                *)
(* ------------------------------------------------------------------------- *)

let rec complete ord (eqs,def,crits) =
  match crits with
    eq::ocrits ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; complete ord trip
  | _ -> if def = [] then eqs else
         let e = find (can (normalize_and_orient ord eqs)) def in
         complete ord (eqs,subtract def [e],[e]);;

(* ------------------------------------------------------------------------- *)
(* A simple "manual" example, before considering packaging and refinements.  *)
(* ------------------------------------------------------------------------- *)

(*
let eqs =
  [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

let ord = lpo_ge (weight ["1"; "*"; "i"]);;

let eqs' = complete ord
  (eqs,[],unions(allpairs critical_pairs eqs eqs));;

rewrite eqs' <<|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Interreduction.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec interreduce dun eqs =
  match eqs with
    (Atom(R("=",[l;r])))::oeqs ->
        let dun' = if rewrite (dun @ oeqs) l <> l then dun
                   else mk_eq l (rewrite (dun @ eqs) r)::dun in
        interreduce dun' oeqs
  | [] -> rev dun;;

(* ------------------------------------------------------------------------- *)
(* This does indeed help a lot.                                              *)
(* ------------------------------------------------------------------------- *)

(*
interreduce [] eqs';;
*)

(* ------------------------------------------------------------------------- *)
(* Overall function with post-simplification (but not dynamically).          *)
(* ------------------------------------------------------------------------- *)

let complete_and_simplify wts eqs =
  let ord = lpo_ge (weight wts) in
  let eqs' = map (fun e -> let l,r = normalize_and_orient ord [] e in
                           mk_eq l r) eqs in
  (interreduce [] ** complete ord)
  (eqs',[],unions(allpairs critical_pairs eqs' eqs'));;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

(*
complete_and_simplify ["1"; "*"; "i"]
  [<<i(a) * (a * b) = b>>];;

(* ------------------------------------------------------------------------- *)
(* Auxiliary result used to justify extension of language for cancellation.  *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 <<(forall x y z. x * y = x * z ==> y = z) <=>
   (forall x z. exists w. forall y. z = x * y ==> w = y)>>;;

skolemize <<forall x z. exists w. forall y. z = x * y ==> w = y>>;;
*)

(* ------------------------------------------------------------------------- *)
(* The commutativity example (of course it fails...).                        *)
(* ------------------------------------------------------------------------- *)

(*******************

#trace complete;;

complete_and_simplify ["1"; "*"; "i"]
 [<<(x * y) * z = x * (y * z)>>;
  <<1 * x = x>>; <<x * 1 = x>>; <<x * x = 1>>];;

 ********************)

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)

(*
let eqs =  [<<(a * b) * (b * c) = b>>];;

complete_and_simplify ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* (l,r)-systems (K&B example 12).                                           *)
(* ------------------------------------------------------------------------- *)

(******** This works, but takes a long time

let eqs =
 [<<(x * y) * z = x * y * z>>; <<1 * x = x>>; <<x * i(x) = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* Auxiliary result used to justify extension for example 9.                 *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 <<(forall x y z. x * y = x * z ==> y = z) <=>
   (forall x z. exists w. forall y. z = x * y ==> w = y)>>;;

skolemize <<forall x z. exists w. forall y. z = x * y ==> w = y>>;;

let eqs =
  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* K&B example 7, where we need to divide through.                           *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(a,f(b,c,a),d) = c>>];;

(*********** Can't orient

complete_and_simplify ["f"] eqs;;

*************)

let eqs =  [<<f(a,f(b,c,a),d) = c>>; <<f(a,b,c) = g(a,b)>>;
                     <<g(a,b) = h(b)>>];;

complete_and_simplify ["h"; "g"; "f"] eqs;;


(* ------------------------------------------------------------------------- *)
(* Other examples not in the book, mostly from K&B                           *)
(* ------------------------------------------------------------------------- *)

(************

(* ------------------------------------------------------------------------- *)
(* Group theory I (K & B example 1).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* However, with the rules in a different order, things take longer.         *)
(* At least we don't need to defer any critical pairs...                     *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>; <<1 * x = x>>; <<i(x) * x = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Example 2: if we orient i(x) * i(y) -> i(x * y), things diverge.          *)
(* ------------------------------------------------------------------------- *)

(**************

let eqs =
 [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

complete_and_simplify ["1"; "i"; "*"] eqs;;
 *************)

(* ------------------------------------------------------------------------- *)
(* Group theory III, with right inverse and identity (K&B example 3).        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>; <<x * 1 = x>>; <<x * i(x) = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<i(a) * (a * b) = b>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

let eqs =  [<<a * (i(a) * b) = b>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Group theory IV (K&B example 5).                                          *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * x = x>>; <<11 * x = x>>;
  <<i(x) * x = 1>>; <<j(x) * x = 11>>];;

complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<(a * b) * (b * c) = b>>];;

complete_and_simplify ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Random axiom (K&B example 7).                                             *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(a,f(b,c,a),d) = c>>];;

(*********** Can't orient

complete_and_simplify ["f"] eqs;;

*************)

let eqs =  [<<f(a,f(b,c,a),d) = c>>; <<f(a,b,c) = g(a,b)>>;
                     <<g(a,b) = h(b)>>];;

complete_and_simplify ["h"; "g"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Another random axiom (K&B example 8).                                     *)
(* ------------------------------------------------------------------------- *)

(************* Can't orient

let eqs =  [<<(a * b) * (c * b * a) = b>>];;

complete_and_simplify ["*"] eqs;;

 *************)

(* ------------------------------------------------------------------------- *)
(* The cancellation law (K&B example 9).                                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>];;

complete_and_simplify ["*"; "f"; "g"] eqs;;

let eqs =
  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(**** Just for fun; these aren't tried by Knuth and Bendix

let eqs =
  [<<(x * y) * z = x * y * z>>;
   <<f(a,a*b) = b>>; <<g(a*b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

let eqs =
  [<<(x * y) * z = x * y * z>>;
   <<f(a,a*b) = b>>; <<g(a*b,b) = a>>];;

complete_and_simplify ["*"; "f"; "g"] eqs;;

complete_and_simplify ["f"; "g"; "*"] eqs;;

*********)

(* ------------------------------------------------------------------------- *)
(* Loops (K&B example 10).                                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<a * \(a,b) = b>>; <</(a,b) * b = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "\\"; "/"] eqs;;

let eqs =
 [<<a * \(a,b) = b>>; <</(a,b) * b = a>>; <<1 * a = a>>; <<a * 1 = a>>;
  <<f(a,a*b) = b>>; <<g(a*b,b) = a>>];;

complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Another variant of groups (K&B example 11).                               *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * 1 = 1>>;
  <<a * i(a) = 1>>;
  <<f(1,a,b) = a>>;
  <<f(a*b,a,b) = g(a*b,b)>>];;

(******** this is not expected to terminate

complete_and_simplify ["1"; "g"; "f"; "*"; "i"] eqs;;

**************)

(* ------------------------------------------------------------------------- *)
(* (l,r)-systems (K&B example 12).                                           *)
(* ------------------------------------------------------------------------- *)

(******** This works, but takes a long time

let eqs =
 [<<(x * y) * z = x * y * z>>; <<1 * x = x>>; <<x * i(x) = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* (r,l)-systems (K&B example 13).                                           *)
(* ------------------------------------------------------------------------- *)

(**** Note that here the simple LPO approach works, whereas K&B need
 **** some additional hacks.
 ****)

let eqs =
 [<<(x * y) * z = x * y * z>>; <<x * 1 = x>>; <<i(x) * x = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* (l,r) systems II (K&B example 14).                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * x = x>>; <<11 * x = x>>;
  <<x * i(x) = 1>>; <<x * j(x) = 11>>];;

(******** This seems to be too slow. K&B encounter a similar problem

complete_and_simplify ["1"; "11"; "*"; "i"; "j"] eqs;;

 ********)

(* ------------------------------------------------------------------------- *)
(* (l,r) systems III (K&B example 15).                                       *)
(* ------------------------------------------------------------------------- *)

(********** According to KB, this wouldn't be expected to work

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * x = x>>;
  <<prime(a) * a = star(a)>>;
  <<star(a) * b = b>>];;

complete_and_simplify ["1"; "*"; "star"; "prime"] eqs;;

 ************)

(*********** These seem too slow too. Maybe just a bad ordering?

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * x = x>>;
  <<hash(a) * dollar(a) * a = star(a)>>;
  <<star(a) * b = b>>;
  <<a * hash(a) = 1>>;
  <<a * 1 = hash(hash(a))>>;
  <<hash(hash(hash(a))) = hash(a)>>];;

complete_and_simplify ["1"; "hash"; "star"; "*"; "dollar"] eqs;;

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<1 * x = x>>;
  <<hash(a) * dollar(a) * a = star(a)>>;
  <<star(a) * b = b>>;
  <<a * hash(a) = 1>>;
  <<hash(hash(a)) = a * 1>>;
  <<hash(hash(hash(a))) = hash(a)>>];;

complete_and_simplify ["1"; "star"; "*"; "hash"; "dollar"] eqs;;

***********)

(* ------------------------------------------------------------------------- *)
(* Central groupoids II. (K&B example 16).                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(a * a) * a = one(a)>>;
  <<a * (a * a) = two(a)>>;
  <<(a * b) * (b * c) = b>>;
  <<two(a) * b = a * b>>];;

complete_and_simplify ["one"; "two"; "*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Central groupoids II. (K&B example 17).                                   *)
(* ------------------------------------------------------------------------- *)

(******** Not ordered right...

let eqs =
 [<<(a*a * a) = one(a)>>;
  <<(a * a*a) = two(a)>>;
  <<(a*b * b*c) = b>>];;

complete_and_simplify ["*"; "one"; "two"] eqs;;

 ************)

(* ------------------------------------------------------------------------- *)
(* Simply congruence closure.                                                *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(f(f(f(f(1))))) = 1>>; <<f(f(f(1))) = 1>>];;

complete_and_simplify ["1"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Bill McCune's and Deepak Kapur's single axioms for groups.                *)
(* ------------------------------------------------------------------------- *)

(*****************

let eqs =
 [<<x * i(y * (((z * i(z)) * i(u * y)) * x)) = u>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

let eqs =
 [<<((1 / (x / (y / (((x / x) / x) / z)))) / z) = y>>];;

complete_and_simplify ["1"; "/"] eqs;;

let eqs =
 [<<i(x * i(x)) * (i(i((y * z) * u) * y) * i(u)) = z>>];;

complete_and_simplify ["*"; "i"] eqs;;

**************)

(* ------------------------------------------------------------------------- *)
(* A rather simple example from Baader & Nipkow, p. 141.                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(f(x)) = g(x)>>];;

complete_and_simplify ["g"; "f"] eqs;;
*)

(* ------------------------------------------------------------------------- *)
(* Step-by-step; note that we *do* deduce commutativity, deferred of course. *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * (y * z)>>; <<1 * x = x>>; <<x * 1 = x>>; <<x * x = 1>>]
and wts = ["1"; "*"; "i"];;

let ord = lpo_ge (weight wts);;

let def = [] and crits = unions(allpairs critical_pairs eqs eqs);;
let complete1 ord (eqs,def,crits) =
  match crits with
    (eq::ocrits) ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; trip
  | _ -> if def = [] then (eqs,def,crits) else
         let e = find (can (normalize_and_orient ord eqs)) def in
         (eqs,subtract def [e],[e]);;

(*
let eqs1,def1,crits1 = funpow 122 (complete1 ord) (eqs,def,crits);;

let eqs2,def2,crits2 = funpow 123 (complete1 ord) (eqs,def,crits);;
*)

(* ------------------------------------------------------------------------- *)
(* Some of the exercises (these are taken from Baader & Nipkow).             *)
(* ------------------------------------------------------------------------- *)

(*
let eqs =
 [<<f(f(x)) = f(x)>>;
  <<g(g(x)) = f(x)>>;
  <<f(g(x)) = g(x)>>;
  <<g(f(x)) = f(x)>>];;

complete_and_simplify ["f"; "g"] eqs;;

let eqs =  [<<f(g(f(x))) = g(x)>>];;

complete_and_simplify ["f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inductive theorem proving example.                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<0 + y = y>>;
  <<SUC(x) + y = SUC(x + y)>>;
  <<append(nil,l) = l>>;
  <<append(h::t,l) = h::append(t,l)>>;
  <<length(nil) = 0>>;
  <<length(h::t) = SUC(length(t))>>;
  <<rev(nil) = nil>>;
  <<rev(h::t) = append(rev(t),h::nil)>>];;

complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs;;

let iprove eqs' tm =
 complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
   (tm :: eqs' @ eqs);;

iprove [] <<x + 0 = x>>;;

iprove [] <<x + SUC(y) = SUC(x + y)>>;;

iprove [] <<(x + y) + z = x + y + z>>;;

iprove [] <<length(append(x,y)) = length(x) + length(y)>>;;

iprove [] <<append(append(x,y),z) = append(x,append(y,z))>>;;

iprove [] <<append(x,nil) = x>>;;

iprove [<<append(append(x,y),z) = append(x,append(y,z))>>;
        <<append(x,nil) = x>>]
        <<rev(append(x,y)) = append(rev(y),rev(x))>>;;

iprove [<<rev(append(x,y)) = append(rev(y),rev(x))>>;
        <<append(x,nil) = x>>;
        <<append(append(x,y),z) = append(x,append(y,z))>>]
        <<rev(rev(x)) = x>>;;

(* ------------------------------------------------------------------------- *)
(* Here it's not immediately so obvious since we get extra equs.             *)
(* ------------------------------------------------------------------------- *)

iprove [] <<rev(rev(x)) = x>>;;

(* ------------------------------------------------------------------------- *)
(* With fewer lemmas, it may just need more time or may not terminate.       *)
(* ------------------------------------------------------------------------- *)

(********* not enough lemmas...or maybe it just needs more runtime

iprove [<<rev(append(x,y)) = append(rev(y),rev(x))>>]
        <<rev(rev(x)) = x>>;;

 *********)

(* ------------------------------------------------------------------------- *)
(* Now something actually false...                                           *)
(* ------------------------------------------------------------------------- *)

iprove [] <<length(append(x,y)) = length(x)>>;; (*** try something false ***)

*************)
*)
(* ========================================================================= *)
(* Equality elimination including Brand transformation and relatives.        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(*

(* ------------------------------------------------------------------------- *)
(* The x^2 = 1 implies Abelian problem.                                      *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(x,x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w)
                        ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* Lemma for equivalence elimination.                                        *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. R(x,x)) /\
   (forall x y. R(x,y) ==>  R(y,x)) /\
   (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
   <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))>>;;

*)

(* ------------------------------------------------------------------------- *)
(* Brand's S and T modifications on clauses.                                 *)
(* ------------------------------------------------------------------------- *)

let rec modify_S cl =
  try let (s,t) = tryfind dest_eq cl in
      let eq1 = mk_eq s t and eq2 = mk_eq t s in
      let sub = modify_S (subtract cl [eq1]) in
      map (insert eq1) sub @ map (insert eq2) sub
  with Failure _ -> [cl];;

let rec modify_T cl =
  match cl with
    (Atom(R("=",[s;t])) as eq)::ps ->
        let ps' = modify_T ps in
        let w = Var(variant "w" (itlist (union ** fv) ps' (fv eq))) in
        Not(mk_eq t w)::(mk_eq s w)::ps'
  | p::ps -> p::(modify_T ps)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Finding nested non-variable subterms.                                     *)
(* ------------------------------------------------------------------------- *)

let is_nonvar = function (Var x) -> false | _ -> true;;

let find_nestnonvar tm =
  match tm with
    Var x -> failwith "findnvsubt"
  | Fn(f,args) -> find is_nonvar args;;

let rec find_nvsubterm fm =
  match fm with
    Atom(R("=",[s;t])) -> tryfind find_nestnonvar [s;t]
  | Atom(R(p,args)) -> find is_nonvar args
  | Not p -> find_nvsubterm p;;

(* ------------------------------------------------------------------------- *)
(* Replacement (substitution for non-variable) in term and literal.          *)
(* ------------------------------------------------------------------------- *)

let rec replacet rfn tm =
  try apply rfn tm with Failure _ ->
  match tm with
    Fn(f,args) -> Fn(f,map (replacet rfn) args)
  | _ -> tm;;

let replace rfn = onformula (replacet rfn);;

(* ------------------------------------------------------------------------- *)
(* E-modification of a clause.                                               *)
(* ------------------------------------------------------------------------- *)

let rec emodify fvs cls =
  try let t = tryfind find_nvsubterm cls in
      let w = variant "w" fvs in
      let cls' = map (replace (t |=> Var w)) cls in
      emodify (w::fvs) (Not(mk_eq t (Var w))::cls')
  with Failure _ -> cls;;

let modify_E cls = emodify (itlist (union ** fv) cls []) cls;;

(* ------------------------------------------------------------------------- *)
(* Overall Brand transformation.                                             *)
(* ------------------------------------------------------------------------- *)

let brand cls =
  let cls1 = map modify_E cls in
  let cls2 = itlist (union ** modify_S) cls1 [] in
  [mk_eq (Var "x") (Var "x")]::(map modify_T cls2);;

(* ------------------------------------------------------------------------- *)
(* Incorporation into MESON.                                                 *)
(* ------------------------------------------------------------------------- *)

let bpuremeson fm =
  let cls = brand(simpcnf(specialize(pnf fm))) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     mexpand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let bmeson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (bpuremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
time bmeson
 <<(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>          
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')>>;;          
                                                                               
time emeson                                                            
 <<(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>           
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')>>;;        
                                                            
time bmeson
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. e * x = x) /\  
   (forall x. i(x) * x = e)                                              
   ==> forall x. x * i(x) = e>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Older stuff not now in the text.                                          *)
(* ------------------------------------------------------------------------- *)

(*
let emeson fm = meson (equalitize fm);;

let ewd =
 <<(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)>>;;

let wishnu =
 <<(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')>>;;

let group1 =
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. e * x = x) /\
   (forall x. i(x) * x = e)
   ==> forall x. x * e = x>>;;

let group2 =
 <<(forall x y z. x * (y * z) = (x * y) * z) /\
   (forall x. e * x = x) /\
   (forall x. i(x) * x = e)
   ==> forall x. x * i(x) = e>>;;

time bmeson ewd;;
time emeson ewd;;

(***********

time bmeson wishnu;;
time emeson wishnu;;

time bmeson group1;;
time emeson group1;;

time bmeson group2;;
time emeson group2;;

 *************)

(* ------------------------------------------------------------------------- *)
(* Nice function composition exercise from "Conceptual Mathematics".         *)
(* ------------------------------------------------------------------------- *)

(**************

let fm =
 <<(forall x y z. x * (y * z) = (x * y) * z) /\ p * q * p = p
   ==> exists q'. p * q' * p = p /\ q' * p * q' = q'>>;;

time bmeson fm;;        (** Seems to take a bit longer than below version  **)

time emeson fm;;        (** Works in 64275 seconds(!), depth 30, on laptop **)

****************)

(**** Some other predicate formulations no longer in the main text

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(i(x),x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall x. P(x,1,x)>>;;

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(i(x),x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall x. P(x,i(x),1)>>;;

(* ------------------------------------------------------------------------- *)
(* See how efficiency drops when we assert completeness.                     *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(x,x,1)) /\
   (forall x y. exists z. P(x,y,z)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

****)

(*** More reductions, not now explicitly in the text.

meson
 <<(forall x. R(x,x)) /\
   (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
   <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))>>;;

meson
 <<(forall x y. R(x,y) ==>  R(y,x)) <=>
   (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))>>;;

(* ------------------------------------------------------------------------- *)
(* Show how Equiv' reduces to triviality.                                    *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. (forall w. R'(x,w) <=> R'(x,w))) /\
   (forall x y. (forall w. R'(x,w) <=> R'(y,w))
                ==> (forall w. R'(y,w) <=> R'(x,w))) /\
   (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\
                  (forall w. R'(y,w) <=> R'(z,w))
                  ==> (forall w. R'(x,w) <=> R'(z,w)))>>;;

(* ------------------------------------------------------------------------- *)
(* More auxiliary proofs for Brand's S and T modification.                   *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\
   (forall x. R'(x,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;

meson
 <<(forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\
   (forall x. R'(x,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;

meson
 <<(forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;

***)

*)
(* ========================================================================= *)
(* Paramodulation.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Find paramodulations with l = r inside a literal fm.                      *)
(* ------------------------------------------------------------------------- *)

let rec overlapl (l,r) fm rfn =
  match fm with
    Atom(R(f,args)) -> listcases (overlaps (l,r))
                              (fun i a -> rfn i (Atom(R(f,a)))) args []
  | Not(p) -> overlapl (l,r) p (fun i p -> rfn i (Not(p)))
  | _ -> failwith "overlapl: not a literal";;

(* ------------------------------------------------------------------------- *)
(* Now find paramodulations within a clause.                                 *)
(* ------------------------------------------------------------------------- *)

let overlapc (l,r) cl rfn acc = listcases (overlapl (l,r)) rfn cl acc;;

(* ------------------------------------------------------------------------- *)
(* Overall paramodulation of ocl by equations in pcl.                        *)
(* ------------------------------------------------------------------------- *)

let paramodulate pcl ocl =
  itlist (fun eq -> let pcl' = subtract pcl [eq] in
                    let (l,r) = dest_eq eq
                    and rfn i ocl' = image (subst i) (pcl' @ ocl') in
                    overlapc (l,r) ocl rfn ** overlapc (r,l) ocl rfn)
         (filter is_eq pcl) [];;

let para_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  paramodulate cls1' cls2' @ paramodulate cls2' cls1';;

(* ------------------------------------------------------------------------- *)
(* Incorporation into resolution loop.                                       *)
(* ------------------------------------------------------------------------- *)

let rec paraloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cls::ros ->
        print_string(string_of_int(length used) ^ " used; "^
                     string_of_int(length unused) ^ " unused.");
        print_newline();
        let used' = insert cls used in
        let news =
          itlist (@) (mapfilter (resolve_clauses cls) used')
            (itlist (@) (mapfilter (para_clauses cls) used') []) in
        if mem [] news then true else
        paraloop(used',itlist (incorporate cls) news ros);;

let pure_paramodulation fm =
  paraloop([],[mk_eq (Var "x") (Var "x")]::
              simpcnf(specialize(pnf fm)));;

let paramodulation fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_paramodulation ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Test.                                                                     *)
(* ------------------------------------------------------------------------- *)

(*
paramodulation
 <<(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
   ==> forall x. f(x) = x>>;;
*)
(* ========================================================================= *)
(* Special procedures for decidable subsets of first order logic.            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(***
meson <<forall x. p(x)>>;;
tab <<forall x. p(x)>>;;
 ***)

(* ------------------------------------------------------------------------- *)
(* Resolution does actually terminate with failure in simple cases!          *)
(* ------------------------------------------------------------------------- *)

(***
resolution <<forall x. p(x)>>;;
 ***)

(* ------------------------------------------------------------------------- *)
(* The Los example; see how Skolemized form has no non-nullary functions.    *)
(* ------------------------------------------------------------------------- *)

(*
let los =
 <<(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
   (forall x y. P(x,y) ==> P(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;
skolemize(Not los);;

(* ------------------------------------------------------------------------- *)
(* The old DP procedure works.                                               *)
(* ------------------------------------------------------------------------- *)

davisputnam los;;
*)

(* ------------------------------------------------------------------------- *)
(* However, we can just form all the ground instances.                       *)
(* ------------------------------------------------------------------------- *)

let aedecide fm =
  let sfm = skolemize(Not fm) in
  let fvs = fv sfm
  and cnsts,funcs = partition (fun (_,ar) -> ar = 0) (functions sfm) in
  if funcs <> [] then failwith "Not decidable" else
  let consts = if cnsts = [] then ["c",0] else cnsts in
  let cntms = map (fun (c,_) -> Fn(c,[])) consts in
  let alltuples = groundtuples cntms [] 0 (length fvs) in
  let cjs = simpcnf sfm in
  let grounds = map
   (fun tup -> image (image (subst (fpf fvs tup))) cjs) alltuples in
  not(dpll(unions grounds));;

(* ------------------------------------------------------------------------- *)
(* In this case it's quicker.                                                *)
(* ------------------------------------------------------------------------- *)

(*
aedecide los;;
*)

(* ------------------------------------------------------------------------- *)
(* Show how we need to do PNF transformation with care.                      *)
(* ------------------------------------------------------------------------- *)

(*
let fm = <<(forall x. p(x)) \/ (exists y. p(y))>>;;

pnf fm;;

(* ------------------------------------------------------------------------- *)
(* Also the group theory problem.                                            *)
(* ------------------------------------------------------------------------- *)

aedecide
 <<(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

aedecide
 <<(forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* A bigger example.                                                         *)
(* ------------------------------------------------------------------------- *)

aedecide
 <<(exists x. P(x)) /\ (exists x. G(x))
   ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* The following, however, doesn't work with aedecide.                       *)
(* ------------------------------------------------------------------------- *)

(*** This is p18

aedecide <<exists y. forall x. P(y) ==> P(x)>>;;

davisputnam <<exists y. forall x. P(y) ==> P(x)>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Simple-minded miniscoping procedure.                                      *)
(* ------------------------------------------------------------------------- *)

let separate x cjs =
  let yes,no = partition (mem x ** fv) cjs in
  if yes = [] then list_conj no
  else if no = [] then Exists(x,list_conj yes)
  else And(Exists(x,list_conj yes),list_conj no);;

let rec pushquant x p =
  if not (mem x (fv p)) then p else
  let djs = purednf(nnf p) in
  list_disj (map (separate x) djs);;

let rec miniscope fm =
  match fm with
    Not p -> Not(miniscope p)
  | And(p,q) -> And(miniscope p,miniscope q)
  | Or(p,q) -> Or(miniscope p,miniscope q)
  | Forall(x,p) -> Not(pushquant x (Not(miniscope p)))
  | Exists(x,p) -> pushquant x (miniscope p)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
miniscope(nnf <<exists y. forall x. P(y) ==> P(x)>>);;

let fm = miniscope(nnf
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>);;

pnf(nnf fm);;
*)

(* ------------------------------------------------------------------------- *)
(* Stronger version of "aedecide" similar to Wang's classic procedure.       *)
(* ------------------------------------------------------------------------- *)

let wang fm = aedecide(miniscope(nnf(simplify fm)));;

(* ------------------------------------------------------------------------- *)
(* It works well on simple monadic formulas.                                 *)
(* ------------------------------------------------------------------------- *)

(*
wang
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

(* ------------------------------------------------------------------------- *)
(* But not on this one!                                                      *)
(* ------------------------------------------------------------------------- *)

pnf(nnf(miniscope(nnf
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>)));;
*)

(* ------------------------------------------------------------------------- *)
(* Checking classic Aristotelean syllogisms.                                 *)
(* ------------------------------------------------------------------------- *)

let atom p x = Atom(R(p,[Var x]));;

let premiss_A (p,q) = Forall("x",Imp(atom p "x",atom q "x"))
and premiss_E (p,q) = Forall("x",Imp(atom p "x",Not(atom q "x")))
and premiss_I (p,q) = Exists("x",And(atom p "x",atom q "x"))
and premiss_O (p,q) = Exists("x",And(atom p "x",Not(atom q "x")));;

let anglicize_premiss fm =
  match fm with
    Forall(_,Imp(Atom(R(p,_)),Atom(R(q,_)))) ->  "all "^p^" are "^q
  | Forall(_,Imp(Atom(R(p,_)),Not(Atom(R(q,_))))) ->  "no "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Atom(R(q,_)))) ->  "some "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Not(Atom(R(q,_))))) ->
        "some "^p^" are not "^q;;

let anglicize_syllogism (Imp(And(t1,t2),t3)) =
  "If " ^ anglicize_premiss t1 ^ " and " ^ anglicize_premiss t2 ^
  ", then " ^ anglicize_premiss t3;;

let all_possible_syllogisms =
  let sylltypes = [premiss_A; premiss_E; premiss_I; premiss_O] in
  let prems1 = allpairs (fun x -> x) sylltypes ["M","P"; "P","M"]
  and prems2 = allpairs (fun x -> x) sylltypes ["S","M"; "M","S"]
  and prems3 = allpairs (fun x -> x) sylltypes ["S","P"] in
  allpairs mk_imp (allpairs mk_and prems1 prems2) prems3;;

(*
let all_valid_syllogisms = filter aedecide all_possible_syllogisms;;

length all_valid_syllogisms;;

map anglicize_syllogism all_valid_syllogisms;;
*)

(* ------------------------------------------------------------------------- *)
(* We can "fix" the traditional list by assuming nonemptiness.               *)
(* ------------------------------------------------------------------------- *)

let all_possible_syllogisms' =
  let p =
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x))>> in
  map (fun t -> Imp(p,t)) all_possible_syllogisms;;

(*
let all_valid_syllogisms' = filter aedecide all_possible_syllogisms';;

length all_valid_syllogisms';;

map (anglicize_syllogism ** consequent) all_valid_syllogisms';;
*)

(* ------------------------------------------------------------------------- *)
(* Decide a formula on all models of size n.                                 *)
(* ------------------------------------------------------------------------- *)

let rec alltuples n l =
  if n = 0 then [[]] else
  let tups = alltuples (n - 1) l in
  allpairs (fun h t -> h::t) l tups;;

let allmappings dom ran =
  itlist (fun p -> allpairs (valmod p) ran) dom [undef];;

let alldepmappings dom ran =
  itlist (fun (p,n) -> allpairs (valmod p) (ran n)) dom [undef];;

let allfunctions dom n = allmappings (alltuples n dom) dom;;

let allpredicates dom n = allmappings (alltuples n dom) [false;true];;

let decide_finite n fm =
  let funcs = functions fm and preds = predicates fm and dom = 1--n in
  let fints = alldepmappings funcs (allfunctions dom)
  and pints = alldepmappings preds (allpredicates dom) in
  let interps = allpairs (fun f p -> dom,f,p) fints pints in
  let fm' = generalize fm in
  forall (fun md -> holds md undefined fm') interps;;

(* ------------------------------------------------------------------------- *)
(* Decision procedure in principle for formulas with finite model property.  *)
(* ------------------------------------------------------------------------- *)

let limmeson n fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  mexpand rules [] False (fun x -> x) (undefined,n,0);;

let limited_meson n fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (limmeson n ** list_conj) (simpdnf fm1);;

let decide_fmp fm =
  let rec test n =
    try limited_meson n fm; true with Failure _ ->
    if decide_finite n fm then test (n + 1) else false in
  test 1;;

(*
decide_fmp
 <<(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)>>;;

decide_fmp
 <<(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)>>;;

(*** This fails to terminate: has countermodels, but only infinite ones
decide_fmp
 <<~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;
****)
*)

(* ------------------------------------------------------------------------- *)
(* Semantic decision procedure for the monadic fragment.                     *)
(* ------------------------------------------------------------------------- *)

let decide_monadic fm =
  let funcs = functions fm and preds = predicates fm in
  let monadic,other = partition (fun (_,ar) -> ar = 1) preds in
  if funcs <> [] or exists (fun (_,ar) -> ar > 1) other
  then failwith "Not in the monadic subset" else
  let n = funpow (length monadic) (( * ) 2) 1 in
  decide_finite n fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
decide_monadic
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
   ((exists x. P(x)) <=> (forall y. P(y))))>>;;

(**** This is not feasible
decide_monadic
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
 ****)
*)

(* ------------------------------------------------------------------------- *)
(* Little auxiliary results for failure of finite model property.            *)
(* ------------------------------------------------------------------------- *)

(*

(*** Our claimed equivalences are indeed correct ***)

meson
 <<(exists x y z. forall u.
        R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;

meson
 <<(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))>>;;

(*** The second formula implies the first ***)

meson
<<~((forall x. ~R(x,x)) /\
    (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
  ==> ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;
*)
(* ========================================================================= *)
(* Introduction to quantifier elimination.                                   *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lift procedure given literal modifier, formula normalizer, and a  basic   *)
(* elimination procedure for existential formulas with conjunctive body.     *)
(* ------------------------------------------------------------------------- *)

let qelim bfn x p =
  let cjs = conjuncts p in
  let ycjs,ncjs = partition (mem x ** fv) cjs in
  if ycjs = [] then p else
  let q = bfn (Exists(x,list_conj ycjs)) in
  itlist mk_and ncjs q;;

let lift_qelim afn nfn qfn =
  let rec qelift vars fm =
    match fm with
    | Atom(R(_,_)) -> afn vars fm
    | Not(p) -> Not(qelift vars p)
    | And(p,q) -> And(qelift vars p,qelift vars q)
    | Or(p,q) -> Or(qelift vars p,qelift vars q)
    | Imp(p,q) -> Imp(qelift vars p,qelift vars q)
    | Iff(p,q) -> Iff(qelift vars p,qelift vars q)
    | Forall(x,p) -> Not(qelift vars (Exists(x,Not p)))
    | Exists(x,p) ->
          let djs = disjuncts(nfn(qelift (x::vars) p)) in
          list_disj(map (qelim (qfn vars) x) djs)
    | _ -> fm in
  fun fm -> simplify(qelift (fv fm) (miniscope fm));;

(* ------------------------------------------------------------------------- *)
(* Cleverer (proposisional) NNF with conditional and literal modification.   *)
(* ------------------------------------------------------------------------- *)

let cnnf lfn =
  let rec cnnf fm =
    match fm with
      And(p,q) -> And(cnnf p,cnnf q)
    | Or(p,q) -> Or(cnnf p,cnnf q)
    | Imp(p,q) -> Or(cnnf(Not p),cnnf q)
    | Iff(p,q) -> Or(And(cnnf p,cnnf q),And(cnnf(Not p),cnnf(Not q)))
    | Not(Not p) -> cnnf p
    | Not(And(p,q)) -> Or(cnnf(Not p),cnnf(Not q))
    | Not(Or(And(p,q),And(p',r))) when p' = negate p ->
         Or(cnnf (And(p,Not q)),cnnf (And(p',Not r)))
    | Not(Or(p,q)) -> And(cnnf(Not p),cnnf(Not q))
    | Not(Imp(p,q)) -> And(cnnf p,cnnf(Not q))
    | Not(Iff(p,q)) -> Or(And(cnnf p,cnnf(Not q)),
                          And(cnnf(Not p),cnnf q))
    | _ -> lfn fm in
  simplify ** cnnf ** simplify;;

(* ------------------------------------------------------------------------- *)
(* Initial literal simplifier and intermediate literal modifier.             *)
(* ------------------------------------------------------------------------- *)

let lfn_dlo fm =
  match fm with
    Not(Atom(R("<",[s;t]))) -> Or(Atom(R("=",[s;t])),Atom(R("<",[t;s])))
  | Not(Atom(R("=",[s;t]))) -> Or(Atom(R("<",[s;t])),Atom(R("<",[t;s])))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Simple example of dense linear orderings; this is the base function.      *)
(* ------------------------------------------------------------------------- *)

let dlobasic fm =
  match fm with
    Exists(x,p) ->
      let cjs = subtract (conjuncts p) [Atom(R("=",[Var x;Var x]))] in
      try let eqn = find is_eq cjs in
          let s,t = dest_eq eqn in
          let y = if s = Var x then t else s in
          list_conj(map (subst (x |=> y)) (subtract cjs [eqn]))
      with Failure _ ->
          if mem (Atom(R("<",[Var x;Var x]))) cjs then False else
          let lefts,rights =
            partition (fun (Atom(R("<",[s;t]))) -> t = Var x) cjs in
          let ls = map (fun (Atom(R("<",[l;_]))) -> l) lefts
          and rs = map (fun (Atom(R("<",[_;r]))) -> r) rights in
          list_conj(allpairs (fun l r -> Atom(R("<",[l;r]))) ls rs)
  | _ -> failwith "dlobasic";;

(* ------------------------------------------------------------------------- *)
(* Overall quelim procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let afn_dlo vars fm =
  match fm with
    Atom(R("<=",[s;t])) -> Not(Atom(R("<",[t;s])))
  | Atom(R(">=",[s;t])) -> Not(Atom(R("<",[s;t])))
  | Atom(R(">",[s;t])) -> Atom(R("<",[t;s]))
  | _ -> fm;;

let quelim_dlo =
  lift_qelim afn_dlo (dnf ** cnnf lfn_dlo) (fun v -> dlobasic);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
quelim_dlo <<forall x y. exists z. z < x /\ z < y>>;;

quelim_dlo <<exists z. z < x /\ z < y>>;;

quelim_dlo <<exists z. x < z /\ z < y>>;;

quelim_dlo <<(forall x. x < a ==> x < b)>>;;

quelim_dlo <<forall a b. (forall x. x < a ==> x < b) <=> a <= b>>;;

quelim_dlo <<forall a b. (forall x. x < a <=> x < b) <=> a = b>>;;

quelim_dlo <<exists x y z. forall u.
                 x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)>>;;

(* ------------------------------------------------------------------------- *)
(* More tests (not in the text).                                             *)
(* ------------------------------------------------------------------------- *)

time quelim_dlo <<forall x. exists y. x < y>>;;

time quelim_dlo <<forall x y z. x < y /\ y < z ==> x < z>>;;

time quelim_dlo <<forall x y. x < y \/ (x = y) \/ y < x>>;;

time quelim_dlo <<exists x y. x < y /\ y < x>>;;

time quelim_dlo <<forall x y. exists z. z < x /\ x < y>>;;

time quelim_dlo <<exists z. z < x /\ x < y>>;;

time quelim_dlo <<forall x y. exists z. z < x /\ z < y>>;;

time quelim_dlo <<forall x y. x < y ==> exists z. x < z /\ z < y>>;;

time quelim_dlo
  <<forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)>>;;

time quelim_dlo <<exists x. x = x>>;;

time quelim_dlo <<exists x. x = x /\ x = y>>;;

time quelim_dlo <<exists z. x < z /\ z < y>>;;

time quelim_dlo <<exists z. x <= z /\ z <= y>>;;

time quelim_dlo <<exists z. x < z /\ z <= y>>;;

time quelim_dlo <<forall x y z. exists u. u < x /\ u < y /\ u < z>>;;

time quelim_dlo <<forall y. x < y /\ y < z ==> w < z>>;;

time quelim_dlo <<forall x y. x < y>>;;

time quelim_dlo <<exists z. z < x /\ x < y>>;;

time quelim_dlo <<forall a b. (forall x. x < a ==> x < b) <=> a <= b>>;;

time quelim_dlo <<forall x. x < a ==> x < b>>;;

time quelim_dlo <<forall x. x < a ==> x <= b>>;;

time quelim_dlo <<forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)>>;;

time quelim_dlo <<forall x y. x <= y \/ x > y>>;;

time quelim_dlo <<forall x y. x <= y \/ x < y>>;;
*)
(* ========================================================================= *)
(* Cooper's algorithm for Presburger arithmetic.                             *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let zero = Fn("0",[]);;

(* ------------------------------------------------------------------------- *)
(* Lift operations up to numerals.                                           *)
(* ------------------------------------------------------------------------- *)

let mk_numeral n = Fn(string_of_num n,[]);;

let dest_numeral t =
  match t with
    Fn(ns,[]) -> num_of_string ns
  | _ -> failwith "dest_numeral";;

let is_numeral = can dest_numeral;;

let numeral1 fn n = mk_numeral(fn(dest_numeral n));;

let numeral2 fn m n = mk_numeral(fn (dest_numeral m) (dest_numeral n));;

(* ------------------------------------------------------------------------- *)
(* Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          *)
(*                                                                           *)
(* Note that we're quite strict: the ci must be present even if 1            *)
(* (but if 0 we expect that variable to be omitted) and k must be there      *)
(* even if it's zero. Thus, it's a constant iff not an addition term.        *)
(* ------------------------------------------------------------------------- *)

let rec linear_cmul n tm =
  if n =/ Int 0 then zero else
  match tm with
    Fn("+",[Fn("*",[c; x]); r]) ->
        Fn("+",[Fn("*",[numeral1(( */ ) n) c; x]); linear_cmul n r])
  | k -> numeral1(( */ ) n) k;;

let rec linear_add vars tm1 tm2 =
  match (tm1,tm2) with
   (Fn("+",[Fn("*",[c1; Var x1]); r1]),
    Fn("+",[Fn("*",[c2; Var x2]); r2])) ->
        if x1 = x2 then
          let c = numeral2 (+/) c1 c2 in
          if c = zero then linear_add vars r1 r2
          else Fn("+",[Fn("*",[c; Var x1]); linear_add vars r1 r2])
        else if earlier vars x1 x2 then
          Fn("+",[Fn("*",[c1; Var x1]); linear_add vars r1 tm2])
        else
          Fn("+",[Fn("*",[c2; Var x2]); linear_add vars tm1 r2])
  | (Fn("+",[Fn("*",[c1; Var x1]); r1]),k2) ->
        Fn("+",[Fn("*",[c1; Var x1]); linear_add vars r1 k2])
  | (k1,Fn("+",[Fn("*",[c2; Var x2]); r2])) ->
        Fn("+",[Fn("*",[c2; Var x2]); linear_add vars k1 r2])
  | _ -> numeral2(+/) tm1 tm2;;

let linear_neg tm = linear_cmul (Int(-1)) tm;;

let linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2);;

let linear_mul tm1 tm2 =
  if is_numeral tm1 then linear_cmul (dest_numeral tm1) tm2
  else if is_numeral tm2 then linear_cmul (dest_numeral tm2) tm1
  else failwith "linear_mul: nonlinearity";;

(* ------------------------------------------------------------------------- *)
(* Linearize a term.                                                         *)
(* ------------------------------------------------------------------------- *)

let rec lint vars tm =
  match tm with
    Var(_) -> Fn("+",[Fn("*",[Fn("1",[]); tm]); zero])
  | Fn("-",[t]) -> linear_neg (lint vars t)
  | Fn("+",[s;t]) -> linear_add vars (lint vars s) (lint vars t)
  | Fn("-",[s;t]) -> linear_sub vars (lint vars s) (lint vars t)
  | Fn("*",[s;t]) -> linear_mul (lint vars s) (lint vars t)
  | _ -> if is_numeral tm then tm else failwith "lint: unknown term";;

(* ------------------------------------------------------------------------- *)
(* Linearize the atoms in a formula, and eliminate non-strict inequalities.  *)
(* ------------------------------------------------------------------------- *)

let mkatom vars p t = Atom(R(p,[zero; lint vars t]));;

let linform vars fm =
  match fm with
    Atom(R("divides",[c;t])) ->
        Atom(R("divides",[numeral1 abs_num c; lint vars t]))
  | Atom(R("=",[s;t])) -> mkatom vars "=" (Fn("-",[t;s]))
  | Atom(R("<",[s;t])) -> mkatom vars "<" (Fn("-",[t;s]))
  | Atom(R(">",[s;t])) -> mkatom vars "<" (Fn("-",[s;t]))
  | Atom(R("<=",[s;t])) ->
        mkatom vars "<" (Fn("-",[Fn("+",[t;Fn("1",[])]);s]))
  | Atom(R(">=",[s;t])) ->
        mkatom vars "<" (Fn("-",[Fn("+",[s;Fn("1",[])]);t]))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Post-NNF transformation eliminating negated inequalities.                 *)
(* ------------------------------------------------------------------------- *)

let rec posineq fm =
  match fm with
  | Not(Atom(R("<",[Fn("0",[]); t]))) ->
        Atom(R("<",[zero; linear_sub [] (Fn("1",[])) t]))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Find the LCM of the coefficients of x.                                    *)
(* ------------------------------------------------------------------------- *)

let rec formlcm x fm =
  match fm with
    Atom(R(p,[_;Fn("+",[Fn("*",[c;y]);z])])) when y = x ->
        abs_num(dest_numeral c)
  | Not(p) -> formlcm x p
  | And(p,q) | Or(p,q) -> lcm_num (formlcm x p) (formlcm x q)
  | _ -> Int 1;;

(* ------------------------------------------------------------------------- *)
(* Adjust all coefficients of x in formula; fold in reduction to +/- 1.      *)
(* ------------------------------------------------------------------------- *)

let rec adjustcoeff x l fm =
  match fm with
    Atom(R(p,[d; Fn("+",[Fn("*",[c;y]);z])])) when y = x ->
        let m = l // dest_numeral c in
        let n = if p = "<" then abs_num(m) else m in
        let xtm = Fn("*",[mk_numeral(m // n); x]) in
        Atom(R(p,[linear_cmul (abs_num m) d;
                  Fn("+",[xtm; linear_cmul n z])]))
  | Not(p) -> Not(adjustcoeff x l p)
  | And(p,q) -> And(adjustcoeff x l p,adjustcoeff x l q)
  | Or(p,q) -> Or(adjustcoeff x l p,adjustcoeff x l q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Hence make coefficient of x one in existential formula.                   *)
(* ------------------------------------------------------------------------- *)

let unitycoeff x fm =
  let l = formlcm x fm in
  let fm' = adjustcoeff x l fm in
  if l =/ Int 1 then fm' else
  let xp = Fn("+",[Fn("*",[Fn("1",[]);x]); zero]) in
  And(Atom(R("divides",[mk_numeral l; xp])),adjustcoeff x l fm);;

(* ------------------------------------------------------------------------- *)
(* The "minus infinity" version.                                             *)
(* ------------------------------------------------------------------------- *)

let rec minusinf x fm =
  match fm with
    Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
        when y = x -> False
  | Atom(R("<",[Fn("0",[]); Fn("+",[Fn("*",[pm1;y]);a])])) when y = x ->
        if pm1 = Fn("1",[]) then False else True
  | Not(p) -> Not(minusinf x p)
  | And(p,q) -> And(minusinf x p,minusinf x q)
  | Or(p,q) -> Or(minusinf x p,minusinf x q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* The LCM of all the divisors that involve x.                               *)
(* ------------------------------------------------------------------------- *)

let rec divlcm x fm =
  match fm with
    Atom(R("divides",[d;Fn("+",[Fn("*",[c;y]);a])])) when y = x ->
        dest_numeral d
  | Not(p) -> divlcm x p
  | And(p,q) | Or(p,q) -> lcm_num (divlcm x p) (divlcm x q)
  | _ -> Int 1;;

(* ------------------------------------------------------------------------- *)
(* Construct the B-set.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec bset x fm =
  match fm with
    Not(Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])])))
    when y = x -> [linear_neg a]
  | Atom(R("=",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
    when y = x -> [linear_neg(linear_add [] a (Fn("1",[])))]
  | Atom(R("<",[Fn("0",[]); Fn("+",[Fn("*",[Fn("1",[]);y]);a])]))
    when y = x -> [linear_neg a]
  | Not(p) -> bset x p
  | And(p,q) -> union (bset x p) (bset x q)
  | Or(p,q) -> union (bset x p) (bset x q)
  | _ -> [];;

(* ------------------------------------------------------------------------- *)
(* Replace top variable with another linear form, retaining canonicality.    *)
(* ------------------------------------------------------------------------- *)

let rec linrep vars x t fm =
  match fm with
    Atom(R(p,[d; Fn("+",[Fn("*",[c;y]);a])])) when y = x ->
        let ct = linear_cmul (dest_numeral c) t in
        Atom(R(p,[d; linear_add vars ct a]))
  | Not(p) -> Not(linrep vars x t p)
  | And(p,q) -> And(linrep vars x t p,linrep vars x t q)
  | Or(p,q) -> Or(linrep vars x t p,linrep vars x t q)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Hence the core quantifier elimination procedure.                          *)
(* ------------------------------------------------------------------------- *)

let cooper vars fm =
  match fm with
   Exists(x0,p0) ->
        let x = Var x0 in
        let p = unitycoeff x p0 in
        let p_inf = simplify(minusinf x p) and bs = bset x p
        and js = Int 1 --- divlcm x p in
        let p_element j b =
          linrep vars x (linear_add vars b (mk_numeral j)) p in
        let stage j = list_disj
           (linrep vars x (mk_numeral j) p_inf ::
            map (p_element j) bs) in
        list_disj (map stage js)
  | _ -> failwith "cooper: not an existential formula";;

(* ------------------------------------------------------------------------- *)
(* Evaluation of constant expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let operations =
  ["=",(=/); "<",(</); ">",(>/); "<=",(<=/); ">=",(>=/);
   "divides",(fun x y -> mod_num y x =/ Int 0)];;

let evalc = onatoms
  (fun (R(p,[s;t]) as at) ->
        (try if assoc p operations (dest_numeral s) (dest_numeral t)
             then True else False
         with Failure _ -> Atom at));;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let integer_qelim =
  simplify ** evalc **
  lift_qelim linform (cnnf posineq ** evalc) cooper;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
integer_qelim <<forall x y. ~(2 * x + 1 = 2 * y)>>;;

integer_qelim <<forall x. exists y. 2 * y <= x /\ x < 2 * (y + 1)>>;;

integer_qelim <<exists x y. 4 * x - 6 * y = 1>>;;

integer_qelim <<forall x. ~divides(2,x) /\ divides(3,x-1) <=>
                          divides(12,x-1) \/ divides(12,x-7)>>;;

integer_qelim <<forall x. b < x ==> a <= x>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Natural number version.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec relativize r fm =
  match fm with
    Not(p) -> Not(relativize r p)
  | And(p,q) -> And(relativize r p,relativize r q)
  | Or(p,q) -> Or(relativize r p,relativize r q)
  | Imp(p,q) -> Imp(relativize r p,relativize r q)
  | Iff(p,q) -> Iff(relativize r p,relativize r q)
  | Forall(x,p) -> Forall(x,Imp(r x,relativize r p))
  | Exists(x,p) -> Exists(x,And(r x,relativize r p))
  | _ -> fm;;

let natural_qelim =
  integer_qelim ** relativize(fun x -> Atom(R("<=",[zero; Var x])));;

(*
natural_qelim <<forall d. exists x y. 3 * x + 5 * y = d>>;;
integer_qelim <<forall d. exists x y. 3 * x + 5 * y = d>>;;
natural_qelim <<forall d. d >= 8 ==> exists x y. 3 * x + 5 * y = d>>;;
natural_qelim <<forall d. exists x y. 3 * x - 5 * y = d>>;;

(* ------------------------------------------------------------------------- *)
(* Other tests, not in the main text.                                        *)
(* ------------------------------------------------------------------------- *)

integer_qelim <<exists x y. x > 0 /\ y >= 0 /\ 3 * x - 5 * y = 1>>;;

integer_qelim <<exists x y z. 4 * x - 6 * y = 1>>;;

integer_qelim <<forall x. a < 3 * x ==> b < 3 * x>>;;

time integer_qelim <<forall x y. x <= y ==> 2 * x + 1 < 2 * y>>;;

time integer_qelim <<(exists d. y = 65 * d) ==> (exists d. y = 5 * d)>>;;

time integer_qelim
  <<forall y. (exists d. y = 65 * d) ==> (exists d. y = 5 * d)>>;;

time integer_qelim <<forall x y. ~(2 * x + 1 = 2 * y)>>;;

time integer_qelim
  <<forall x y z. (2 * x + 1 = 2 * y) ==> x + y + z > 129>>;;

time integer_qelim <<forall x. a < x ==> b < x>>;;

time integer_qelim <<forall x. a <= x ==> b < x>>;;

(* ------------------------------------------------------------------------- *)
(* Formula examples from Cooper's paper.                                     *)
(* ------------------------------------------------------------------------- *)

time integer_qelim <<forall a b. exists x. a < 20 * x /\ 20 * x < b>>;;

time integer_qelim <<exists x. a < 20 * x /\ 20 * x < b>>;;

time integer_qelim <<forall b. exists x. a < 20 * x /\ 20 * x < b>>;;

time integer_qelim
  <<forall a. exists b. a < 4 * b + 3 * a \/ (~(a < b) /\ a > b + 1)>>;;

time integer_qelim
  <<exists y. forall x. x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0>>;;

(* ------------------------------------------------------------------------- *)
(* More of my own.                                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim <<forall x y. x >= 0 /\ y >= 0
                  ==> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2>>;;

time integer_qelim <<exists x y. 5 * x + 3 * y = 1>>;;

time integer_qelim <<exists x y. 5 * x + 10 * y = 1>>;;

time integer_qelim <<exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 6 * y = 1>>;;


time integer_qelim <<exists w x y z. 2 * w + 3 * x + 4 * y + 5 * z = 1>>;;

time integer_qelim <<exists x y. x >= 0 /\ y >= 0 /\ 5 * x - 3 * y = 1>>;;

time integer_qelim <<exists x y. x >= 0 /\ y >= 0 /\ 3 * x - 5 * y = 1>>;;

time integer_qelim <<exists x y. x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1>>;;

time integer_qelim
  <<forall x y. ~(x = 0) ==> 5 * y < 6 * x \/ 5 * y > 6 * x>>;;

time integer_qelim
  <<forall x y. ~divides(5,x) /\ ~divides(6,y) ==> ~(6 * x = 5 * y)>>;;

time integer_qelim <<forall x y. ~divides(5,x) ==> ~(6 * x = 5 * y)>>;;

time integer_qelim <<forall x y. ~(6 * x = 5 * y)>>;;

time integer_qelim <<forall x y. 6 * x = 5 * y ==> exists d. y = 3 * d>>;;

time integer_qelim <<6 * x = 5 * y ==> exists d. y = 3 * d>>;;

(* ------------------------------------------------------------------------- *)
(* Positive variant of the Bezout theorem (see the exercise).                *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
  <<forall z. z > 7 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z>>;;

time integer_qelim
  <<forall z. z > 2 ==> exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z>>;;

time integer_qelim
  <<forall z.
        z <= 7
        ==> ((exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) <=>
             ~(exists x y. x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = 7 - z))>>;;

(* ------------------------------------------------------------------------- *)
(* Basic result about congruences.                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
  <<forall x. ~divides(2,x) /\ divides(3,x-1) <=>
              divides(12,x-1) \/ divides(12,x-7)>>;;

time integer_qelim
  <<forall x. ~(exists m. x = 2 * m) /\ (exists m. x = 3 * m + 1) <=>
              (exists m. x = 12 * m + 1) \/ (exists m. x = 12 * m + 7)>>;;

(* ------------------------------------------------------------------------- *)
(* Something else.                                                           *)
(* ------------------------------------------------------------------------- *)

time integer_qelim
 <<forall x.
        ~(divides(2,x))
        ==> divides(4,x-1) \/
            divides(8,x-1) \/
            divides(8,x-3) \/
            divides(6,x-1) \/
            divides(14,x-1) \/
            divides(14,x-9) \/
            divides(14,x-11) \/
            divides(24,x-5) \/
            divides(24,x-11)>>;;

(* ------------------------------------------------------------------------- *)
(* Testing fix for an earlier version with negative result from formlcm.     *)
(* ------------------------------------------------------------------------- *)

(integer_qelim ** generalize)
  <<a + 2 = b /\ v_3 = b - a + 1 /\ v_2 = b - 2 /\ v_1 = 3 ==> false>>;;

(* ------------------------------------------------------------------------- *)
(* Inspired by the Collatz conjecture.                                       *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  <<exists a b. ~(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b)>>;;

integer_qelim
 <<exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
               (a = b)>>;;

(***************

integer_qelim
 <<exists a b. a > 1 /\ b > 1 /\
               ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
               ((2 * a = b) \/ (2 * a = 3 * b + 1))>>;;

let fm = dnf
 <<((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
   ((2 * c = b) \/ (2 * c = 3 * b + 1)) /\
   ((2 * d = c) \/ (2 * d = 3 * c + 1)) /\
   ((2 * e = d) \/ (2 * e = 3 * d + 1)) /\
   ((2 * f = e) \/ (2 * f = 3 * e + 1)) /\
   (f = a)>>;;

let fms =
  map (itlist (fun x p -> Exists(x,And(Atom(R(">",[Var x; Fn("1",[])])),p)))
              ["b"; "c"; "d"; "e"; "f"])
      (disjuncts fm);;

let fm = el 15 fms;;
integer_qelim fm;;

******************)

(* ------------------------------------------------------------------------- *)
(* Bob Constable's "stamp problem".                                          *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  <<forall x. x >= 8 ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v>>;;

integer_qelim
  <<exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v>>;;

integer_qelim
  <<exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 7 * v>>;;

(************ These seem to take a while --- the second may not be feasible
              although the first is not so bad.

integer_qelim
  <<exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 3 * u + 8 * v>>;;

integer_qelim
  <<exists l.
        forall x. x >= l
                  ==> exists u v. u >= 0 /\ v >= 0 /\ x = 7 * u + 8 * v>>;;

****************)

(* ------------------------------------------------------------------------- *)
(* Example from reciprocal mult: (2622 * x)>>16 = x/100 within a range.      *)
(* ------------------------------------------------------------------------- *)

(*********
integer_qelim
  <<forall x q1 q2 r1 r2.
        x < 4699 /\
        2622 * x = 65536 * q1 + r1 /\ 0 <= q1 /\ 0 <= r1 /\ r1 < 65536 /\
        x = 100 * q2 + r2 /\ 0 <= q2 /\ 0 <= r2 /\ r2 < 100
        ==> q1 = q2>>;;
 *********)

(* ------------------------------------------------------------------------- *)
(* Yet more.                                                                 *)
(* ------------------------------------------------------------------------- *)

integer_qelim
  <<forall x y.
        (exists d. x + y = 2 * d) <=>
        ((exists d. x = 2 * d) <=> (exists d. y = 2 * d))>>;;

(**** Landau trick! Is it too slow?

integer_qelim
 <<forall n.
     0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n>>;;

 ****)

*)
(* ========================================================================= *)
(* Complex quantifier elimination (by simple divisibility a la Tarski).      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic arithmetic operations on canonical polynomials.                     *)
(* ------------------------------------------------------------------------- *)

let rec poly_add vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_ladd vars pol2 pol1
        else if earlier vars y x then poly_ladd vars pol1 pol2 else
        let e = poly_add vars c d and r = poly_add vars p q in
        if r = zero then e else Fn("+",[e; Fn("*",[Var x; r])])
    | (_,Fn("+",_)) -> poly_ladd vars pol1 pol2
    | (Fn("+",_),pol2) -> poly_ladd vars pol2 pol1
    | _ -> numeral2 (+/) pol1 pol2
and poly_ladd vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        Fn("+",[poly_add vars pol1 d; Fn("*",[Var y; q])]);;

let rec poly_neg =
  function (Fn("+",[c; Fn("*",[Var x; p])])) ->
                Fn("+",[poly_neg c; Fn("*",[Var x; poly_neg p])])
         | n -> numeral1 minus_num n;;

let poly_sub vars p q = poly_add vars p (poly_neg q);;

let rec poly_mul vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_lmul vars pol2 pol1
        else poly_lmul vars pol1 pol2
  | (Fn("0",[]),_) | (_,Fn("0",[])) -> zero
  | (_,Fn("+",_)) -> poly_lmul vars pol1 pol2
  | (Fn("+",_),_) -> poly_lmul vars pol2 pol1
  | _ -> numeral2 ( */ ) pol1 pol2
and poly_lmul vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        poly_add vars (poly_mul vars pol1 d)
                     (Fn("+",[zero;
                              Fn("*",[Var y; poly_mul vars pol1 q])]));;

let poly_pow vars p n = funpow n (poly_mul vars p) (Fn("1",[]));;

let poly_div vars p q = poly_mul vars p (numeral1((//) (Int 1)) q);;

let poly_var x = Fn("+",[zero; Fn("*",[Var x; Fn("1",[])])]);;

(* ------------------------------------------------------------------------- *)
(* Convert term into canonical polynomial representative.                    *)
(* ------------------------------------------------------------------------- *)

let rec polynate vars tm =
  match tm with
    Var x -> poly_var x
  | Fn("-",[t]) -> poly_neg (polynate vars t)
  | Fn("+",[s;t]) -> poly_add vars (polynate vars s) (polynate vars t)
  | Fn("-",[s;t]) -> poly_sub vars (polynate vars s) (polynate vars t)
  | Fn("*",[s;t]) -> poly_mul vars (polynate vars s) (polynate vars t)
  | Fn("/",[s;t]) -> poly_div vars (polynate vars s) (polynate vars t)
  | Fn("^",[p;Fn(n,[])]) ->
                     poly_pow vars (polynate vars p) (int_of_string n)
  | _ -> if is_numeral tm then tm else failwith "lint: unknown term";;

(* ------------------------------------------------------------------------- *)
(* Do likewise for atom so the RHS is zero.                                  *)
(* ------------------------------------------------------------------------- *)

let polyatom vars fm =
  match fm with
    Atom(R(a,[s;t])) -> Atom(R(a,[polynate vars (Fn("-",[s;t]));zero]))
  | _ -> failwith "polyatom: not an atom";;

(* ------------------------------------------------------------------------- *)
(* Sanity check.                                                             *)
(* ------------------------------------------------------------------------- *)

(*
polyatom ["w"; "x"; "y"; "z"]
  <<((w + x)^4 + (w + y)^4 + (w + z)^4 +
     (x + y)^4 + (x + z)^4 + (y + z)^4 +
     (w - x)^4 + (w - y)^4 + (w - z)^4 +
     (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
    (w^2 + x^2 + y^2 + z^2)^2>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Useful utility functions for polynomial terms.                            *)
(* ------------------------------------------------------------------------- *)

let rec coefficients vars =
  function Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
                c::(coefficients vars q)
         | p -> [p];;

let degree vars p = length(coefficients vars p) - 1;;

let is_constant vars p = degree vars p = 0;;

let head vars p = last(coefficients vars p);;

let rec behead vars =
  function Fn("+",[c; Fn("*",[Var x; p])]) when x = hd vars ->
        let p' = behead vars p in
        if p' = zero then c else Fn("+",[c; Fn("*",[Var x; p'])])
  | _ -> zero;;

(* ------------------------------------------------------------------------- *)
(* Get the constant multiple of the "maximal" monomial (implicit lex order)  *)
(* ------------------------------------------------------------------------- *)

let rec poly_cmul k p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) ->
        Fn("+",[poly_cmul k c; Fn("*",[Var x; poly_cmul k q])])
  | _ -> numeral1 (fun m -> k */ m) p;;

let rec headconst p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) -> headconst q
  | Fn(n,[]) -> dest_numeral p;;

(* ------------------------------------------------------------------------- *)
(* Make a polynomial monic and return negativity flag for head constant      *)
(* ------------------------------------------------------------------------- *)

let monic p =
  let h = headconst p in
  if h =/ Int 0 then p,false else poly_cmul (Int 1 // h) p,h </ Int 0;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division of s by p; head coefficient of p assumed nonzero.         *)
(* Returns (k,r) so that a^k s = p q + r for some q, deg(r) < deg(p).        *)
(* Optimized only for the trivial case of equal head coefficients; no GCDs.  *)
(* ------------------------------------------------------------------------- *)

let pdivide =
  let shift1 x p = Fn("+",[zero; Fn("*",[Var x; p])]) in
  let rec pdivide_aux vars a n p k s =
    if s = zero then (k,s) else
    let b = head vars s and m = degree vars s in
    if m < n then (k,s) else
    let p' = funpow (m - n) (shift1 (hd vars)) p in
    if a = b then pdivide_aux vars a n p k (poly_sub vars s p')
    else pdivide_aux vars a n p (k+1)
          (poly_sub vars (poly_mul vars a s) (poly_mul vars b p')) in
  fun vars s p -> pdivide_aux vars (head vars p) (degree vars p) p 0 s;;

(* ------------------------------------------------------------------------- *)
(* Datatype of signs.                                                        *)
(* ------------------------------------------------------------------------- *)

type sign = Zero | Nonzero | Positive | Negative;;

let swap swf s =
  if not swf then s else
  match s with
    Positive -> Negative
  | Negative -> Positive
  | _ -> s;;

(* ------------------------------------------------------------------------- *)
(* Lookup and asserting of polynomial sign, modulo constant multiples.       *)
(* Note that we are building in a characteristic-zero assumption here.       *)
(* ------------------------------------------------------------------------- *)

let findsign sgns p =
  try let p',swf = monic p in swap swf (assoc p' sgns)
  with Failure _ -> failwith "findsign";;

let assertsign sgns (p,s) =
  if p = zero then if s = Zero then sgns else failwith "assertsign" else
  let p',swf = monic p in
  let s' = swap swf s in
  let s0 = try assoc p' sgns with Failure _ -> s' in
  if s' = s0 or s0 = Nonzero & (s' = Positive or s' = Negative)
  then (p',s')::(subtract sgns [p',s0]) else failwith "assertsign";;

(* ------------------------------------------------------------------------- *)
(* Deduce or case-split over zero status of polynomial.                      *)
(* ------------------------------------------------------------------------- *)

let split_zero sgns pol cont_z cont_n =
  try let z = findsign sgns pol in
      (if z = Zero then cont_z else cont_n) sgns
  with Failure "findsign" ->
      let eq = Atom(R("=",[pol; zero])) in
      Or(And(eq,cont_z (assertsign sgns (pol,Zero))),
         And(Not eq,cont_n (assertsign sgns (pol,Nonzero))));;

(* ------------------------------------------------------------------------- *)
(* Whether a polynomial is nonzero in a context.                             *)
(* ------------------------------------------------------------------------- *)

let poly_nonzero vars sgns pol =
  let cs = coefficients vars pol in
  let dcs,ucs = partition (can (findsign sgns)) cs in
  if exists (fun p -> findsign sgns p <> Zero) dcs then True
  else if ucs = [] then False else
  end_itlist mk_or (map (fun p -> Not(mk_eq p zero)) ucs);;

(* ------------------------------------------------------------------------- *)
(* Non-divisibility of q by p.                                               *)
(* ------------------------------------------------------------------------- *)

let rec poly_nondiv vars sgns p s =
  let _,r = pdivide vars s p in poly_nonzero vars sgns r;;

(* ------------------------------------------------------------------------- *)
(* Main reduction for exists x. all eqs = 0 and all neqs =/= 0, in context.  *)
(* ------------------------------------------------------------------------- *)

let rec cqelim vars (eqs,neqs) sgns =
  try let c = find (is_constant vars) eqs in
     (try let sgns' = assertsign sgns (c,Zero)
          and eqs' = subtract eqs [c] in
          And(mk_eq c zero,cqelim vars (eqs',neqs) sgns')
      with Failure "assertsign" -> False)
  with Failure _ ->
     if eqs = [] then list_conj(map (poly_nonzero vars sgns) neqs) else
     let n = end_itlist min (map (degree vars) eqs) in
     let p = find (fun p -> degree vars p = n) eqs in
     let oeqs = subtract eqs [p] in
     split_zero sgns (head vars p)
       (cqelim vars (behead vars p::oeqs,neqs))
       (fun sgns' ->
          let cfn s = snd(pdivide vars s p) in
          if oeqs <> [] then cqelim vars (p::(map cfn oeqs),neqs) sgns'
          else if neqs = [] then True else
          let q = end_itlist (poly_mul vars) neqs in
          poly_nondiv vars sgns' p (poly_pow vars q (degree vars p)));;

(* ------------------------------------------------------------------------- *)
(* Basic complex quantifier elimination on actual existential formula.       *)
(* ------------------------------------------------------------------------- *)

let init_sgns = [Fn("1",[]),Positive; Fn("0",[]),Zero];;

let basic_complex_qelim vars (Exists(x,p)) =
  let eqs,neqs = partition (non negative) (conjuncts p) in
  cqelim (x::vars) (map lhs eqs,map (lhs ** negate) neqs) init_sgns;;

(* ------------------------------------------------------------------------- *)
(* Full quantifier elimination.                                              *)
(* ------------------------------------------------------------------------- *)

let complex_qelim =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
             basic_complex_qelim;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0>>;;

complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0>>;;

complex_qelim
 <<forall c.
     (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0)
     <=> c = 1>>;;

complex_qelim
 <<forall a b c x y.
      a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

(* ------------------------------------------------------------------------- *)
(* More tests, not in the main text.                                         *)
(* ------------------------------------------------------------------------- *)

let polytest tm = time (polynate (fvt tm)) tm;;

let lagrange_4 = polytest
 <<|(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))|>>;;

let lagrange_8 = polytest
 <<|((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)|>>;;

let liouville = polytest
 <<|6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))|>>;;

let fleck = polytest
 <<|60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
      (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
      (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
      (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
      (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
      (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
      (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
      (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
     2 * ((x1 + x2)^6 + (x1 - x2)^6 +
          (x1 + x3)^6 + (x1 - x3)^6 +
          (x1 + x4)^6 + (x1 - x4)^6 +
          (x2 + x3)^6 + (x2 - x3)^6 +
          (x2 + x4)^6 + (x2 - x4)^6 +
          (x3 + x4)^6 + (x3 - x4)^6) +
     36 * (x1^6 + x2^6 + x3^6 + x4^6))|>>;;

let hurwitz = polytest
 <<|5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
    (6 * ((x1 + x2 + x3 + x4)^8 +
          (x1 + x2 + x3 - x4)^8 +
          (x1 + x2 - x3 + x4)^8 +
          (x1 + x2 - x3 - x4)^8 +
          (x1 - x2 + x3 + x4)^8 +
          (x1 - x2 + x3 - x4)^8 +
          (x1 - x2 - x3 + x4)^8 +
          (x1 - x2 - x3 - x4)^8) +
     ((2 * x1 + x2 + x3)^8 +
      (2 * x1 + x2 - x3)^8 +
      (2 * x1 - x2 + x3)^8 +
      (2 * x1 - x2 - x3)^8 +
      (2 * x1 + x2 + x4)^8 +
      (2 * x1 + x2 - x4)^8 +
      (2 * x1 - x2 + x4)^8 +
      (2 * x1 - x2 - x4)^8 +
      (2 * x1 + x3 + x4)^8 +
      (2 * x1 + x3 - x4)^8 +
      (2 * x1 - x3 + x4)^8 +
      (2 * x1 - x3 - x4)^8 +
      (2 * x2 + x3 + x4)^8 +
      (2 * x2 + x3 - x4)^8 +
      (2 * x2 - x3 + x4)^8 +
      (2 * x2 - x3 - x4)^8 +
      (x1 + 2 * x2 + x3)^8 +
      (x1 + 2 * x2 - x3)^8 +
      (x1 - 2 * x2 + x3)^8 +
      (x1 - 2 * x2 - x3)^8 +
      (x1 + 2 * x2 + x4)^8 +
      (x1 + 2 * x2 - x4)^8 +
      (x1 - 2 * x2 + x4)^8 +
      (x1 - 2 * x2 - x4)^8 +
      (x1 + 2 * x3 + x4)^8 +
      (x1 + 2 * x3 - x4)^8 +
      (x1 - 2 * x3 + x4)^8 +
      (x1 - 2 * x3 - x4)^8 +
      (x2 + 2 * x3 + x4)^8 +
      (x2 + 2 * x3 - x4)^8 +
      (x2 - 2 * x3 + x4)^8 +
      (x2 - 2 * x3 - x4)^8 +
      (x1 + x2 + 2 * x3)^8 +
      (x1 + x2 - 2 * x3)^8 +
      (x1 - x2 + 2 * x3)^8 +
      (x1 - x2 - 2 * x3)^8 +
      (x1 + x2 + 2 * x4)^8 +
      (x1 + x2 - 2 * x4)^8 +
      (x1 - x2 + 2 * x4)^8 +
      (x1 - x2 - 2 * x4)^8 +
      (x1 + x3 + 2 * x4)^8 +
      (x1 + x3 - 2 * x4)^8 +
      (x1 - x3 + 2 * x4)^8 +
      (x1 - x3 - 2 * x4)^8 +
      (x2 + x3 + 2 * x4)^8 +
      (x2 + x3 - 2 * x4)^8 +
      (x2 - x3 + 2 * x4)^8 +
      (x2 - x3 - 2 * x4)^8) +
     60 * ((x1 + x2)^8 + (x1 - x2)^8 +
           (x1 + x3)^8 + (x1 - x3)^8 +
           (x1 + x4)^8 + (x1 - x4)^8 +
           (x2 + x3)^8 + (x2 - x3)^8 +
           (x2 + x4)^8 + (x2 - x4)^8 +
           (x3 + x4)^8 + (x3 - x4)^8) +
     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))|>>;;

let schur = polytest
 <<|22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
    (9 * ((2 * x1)^10 +
          (2 * x2)^10 +
          (2 * x3)^10 +
          (2 * x4)^10) +
     180 * ((x1 + x2)^10 + (x1 - x2)^10 +
            (x1 + x3)^10 + (x1 - x3)^10 +
            (x1 + x4)^10 + (x1 - x4)^10 +
            (x2 + x3)^10 + (x2 - x3)^10 +
            (x2 + x4)^10 + (x2 - x4)^10 +
            (x3 + x4)^10 + (x3 - x4)^10) +
     ((2 * x1 + x2 + x3)^10 +
      (2 * x1 + x2 - x3)^10 +
      (2 * x1 - x2 + x3)^10 +
      (2 * x1 - x2 - x3)^10 +
      (2 * x1 + x2 + x4)^10 +
      (2 * x1 + x2 - x4)^10 +
      (2 * x1 - x2 + x4)^10 +
      (2 * x1 - x2 - x4)^10 +
      (2 * x1 + x3 + x4)^10 +
      (2 * x1 + x3 - x4)^10 +
      (2 * x1 - x3 + x4)^10 +
      (2 * x1 - x3 - x4)^10 +
      (2 * x2 + x3 + x4)^10 +
      (2 * x2 + x3 - x4)^10 +
      (2 * x2 - x3 + x4)^10 +
      (2 * x2 - x3 - x4)^10 +
      (x1 + 2 * x2 + x3)^10 +
      (x1 + 2 * x2 - x3)^10 +
      (x1 - 2 * x2 + x3)^10 +
      (x1 - 2 * x2 - x3)^10 +
      (x1 + 2 * x2 + x4)^10 +
      (x1 + 2 * x2 - x4)^10 +
      (x1 - 2 * x2 + x4)^10 +
      (x1 - 2 * x2 - x4)^10 +
      (x1 + 2 * x3 + x4)^10 +
      (x1 + 2 * x3 - x4)^10 +
      (x1 - 2 * x3 + x4)^10 +
      (x1 - 2 * x3 - x4)^10 +
      (x2 + 2 * x3 + x4)^10 +
      (x2 + 2 * x3 - x4)^10 +
      (x2 - 2 * x3 + x4)^10 +
      (x2 - 2 * x3 - x4)^10 +
      (x1 + x2 + 2 * x3)^10 +
      (x1 + x2 - 2 * x3)^10 +
      (x1 - x2 + 2 * x3)^10 +
      (x1 - x2 - 2 * x3)^10 +
      (x1 + x2 + 2 * x4)^10 +
      (x1 + x2 - 2 * x4)^10 +
      (x1 - x2 + 2 * x4)^10 +
      (x1 - x2 - 2 * x4)^10 +
      (x1 + x3 + 2 * x4)^10 +
      (x1 + x3 - 2 * x4)^10 +
      (x1 - x3 + 2 * x4)^10 +
      (x1 - x3 - 2 * x4)^10 +
      (x2 + x3 + 2 * x4)^10 +
      (x2 + x3 - 2 * x4)^10 +
      (x2 - x3 + 2 * x4)^10 +
      (x2 - x3 - 2 * x4)^10) +
     9 * ((x1 + x2 + x3 + x4)^10 +
          (x1 + x2 + x3 - x4)^10 +
          (x1 + x2 - x3 + x4)^10 +
          (x1 + x2 - x3 - x4)^10 +
          (x1 - x2 + x3 + x4)^10 +
          (x1 - x2 + x3 - x4)^10 +
          (x1 - x2 - x3 + x4)^10 +
          (x1 - x2 - x3 - x4)^10))|>>;;

let complex_qelim_all = time complex_qelim ** generalize;;

time complex_qelim <<exists x. x + 2 = 3>>;;

time complex_qelim <<exists x. x^2 + a = 3>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0>>;;

time complex_qelim <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0>>;;

time complex_qelim <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim <<exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim <<forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<exists a b c x y.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y) /\
        ~(a * x * y = c)>>;;

(*** This works by a combination with grobner_decide but seems slow like this:

complex_qelim
 <<forall a b c x y.
      ~(a = 0) /\
      (forall z. a * z^2 + b * z + c = 0 <=> z = x) /\ x = y
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

 *** and w/o the condition, it's false I think

complex_qelim
 <<forall a b c x y.
      (forall z. a * z^2 + b * z + c = 0 <=> z = x \/ z = y)
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

 *** because the following is!

 ***)

complex_qelim
 <<forall a b c x.
        (forall z. a * z^2 + b * z + c = 0 <=> z = x)
        ==> a * x * x = c /\ a * (x + x) + b = 0>>;;

(*** In fact we have this, tho' I don't know if that's interesting ***)

complex_qelim
 <<forall x y.
    (forall a b c. (a * x^2 + b * x + c = 0) /\
                   (a * y^2 + b * y + c = 0)
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
    <=> ~(x = y)>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall x y. x^2 = 2 /\ y^2 = 3
         ==> (x * y)^2 = 6>>;;

time complex_qelim
 <<forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<~(exists a x y. (a^2 = 2) /\
             (x^2 + a * x + 1 = 0) /\
             (y * (x^4 + 1) + 1 = 0))>>;;

time complex_qelim <<forall x. exists y. x^2 = y^3>>;;

time complex_qelim
 <<forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               2 * (b * x + b * z - a * y)>>;;

time complex_qelim
 <<forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)>>;;

time complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
                 (a * y^2 + b * y + c = 0)
                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall a1 b1 c1 a2 b2 c2.
        ~(a1 * b2 = a2 * b1)
        ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)>>;;

(* ------------------------------------------------------------------------- *)
(* This seems harder, so see how many quantifiers are feasible.              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<(a * x^2 + b * x + c = 0) /\
  (a * y^2 + b * y + c = 0) /\
  (forall z. (a * z^2 + b * z + c = 0)
       ==> (z = x) \/ (z = y))
  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<forall y. (a * x^2 + b * x + c = 0) /\
            (a * y^2 + b * y + c = 0) /\
            (forall z. (a * z^2 + b * z + c = 0)
                       ==> (z = x) \/ (z = y))
            ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

(**** feasible but lengthy?

time complex_qelim
 <<forall x y. (a * x^2 + b * x + c = 0) /\
              (a * y^2 + b * y + c = 0) /\
              (forall z. (a * z^2 + b * z + c = 0)
                         ==> (z = x) \/ (z = y))
              ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<forall c x y. (a * x^2 + b * x + c = 0) /\
              (a * y^2 + b * y + c = 0) /\
              (forall z. (a * z^2 + b * z + c = 0)
                         ==> (z = x) \/ (z = y))
              ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

 ************)

(********* This seems too hard

time complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               (forall z. (a * z^2 + b * z + c = 0)
                    ==> (z = x) \/ (z = y))
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

 **************)

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3.
      exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\
                    (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)>>;;

time complex_qelim
 <<forall a b c.
      (exists x y. (a * x^2 + b * x + c = 0) /\
             (a * y^2 + b * y + c = 0) /\
             ~(x = y)) <=>
      (a = 0) /\ (b = 0) /\ (c = 0) \/
      ~(a = 0) /\ ~(b^2 = 4 * a * c)>>;;

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0')>>;;

time complex_qelim
 <<forall a b c.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y)
        ==> a * (x + y) + b = 0>>;;

time complex_qelim
 <<forall a b c.
        (a * x^2 + b * x + c = 0) /\
        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\
        ~(x = y)
        ==> (a * (x + y) + b = 0)>>;;

complex_qelim_all
 <<~(y_1 = 2 * y_3 /\
    y_2 = 2 * y_4 /\
    y_1 * y_3 = y_2 * y_4 /\
    (y_1^2 - y_2^2) * z = 1)>>;;

time complex_qelim <<forall y_1 y_2 y_3 y_4.
       (y_1 = 2 * y_3) /\
       (y_2 = 2 * y_4) /\
       (y_1 * y_3 = y_2 * y_4)
       ==> (y_1^2 = y_2^2)>>;;

(************

complex_qelim_all
 <<~((c^2 = a^2 + b^2) /\
     (c^2 = x0^2 + (y0 - b)^2) /\
     (y0 * t1 = a + x0) /\
     (y0 * t2 = a - x0) /\
     ((1 - t1 * t2) * t = t1 + t2) /\
     (u * (b * t - a) = 1) /\
     (v1 * a + v2 * x0 + v3 * y0 = 1))>>;;

complex_qelim_all
 <<(c^2 = a^2 + b^2) /\
   (c^2 = x0^2 + (y0 - b)^2) /\
   (y0 * t1 = a + x0) /\
   (y0 * t2 = a - x0) /\
   ((1 - t1 * t2) * t = t1 + t2) /\
   (~(a = 0) \/ ~(x0 = 0) \/ ~(y0 = 0))
   ==> (b * t = a)>>;;

*********)

complex_qelim_all
 <<(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)>>;;

complex_qelim_all
 <<(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)>>;;

complex_qelim_all
 <<(y1 * y3 + x1 * x3 = 0) /\
  (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\
  ~(x3 = 0) /\
  ~(y3 = 0)
  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))>>;;

(**********

complex_qelim_all
 <<(2 * u2 * x2 + 2 * u3 * x1 - u3^2 - u2^2 = 0) /\
  (2 * u1 * x2 - u1^2 = 0) /\
  (-(x3^2) + 2 * x2 * x3 + 2 * u4 * x1 - u4^2 = 0) /\
  (u3 * x5 + (-(u2) + u1) * x4 - u1 * u3 = 0) /\
  ((u2 - u1) * x5 + u3 * x4 + (-(u2) + u1) * x3 - u3 * u4 = 0) /\
  (u3 * x7 - u2 * x6 = 0) /\
  (u2 * x7 + u3 * x6 - u2 * x3 - u3 * u4 = 0) /\
  ~(4 * u1 * u3 = 0) /\
  ~(2 * u1 = 0) /\
  ~(-(u3^2) - u2^2 + 2 * u1 * u2 - u1^2 = 0) /\
  ~(u3 = 0) /\
  ~(-(u3^2) - u2^2 = 0) /\
  ~(u2 = 0)
  ==> (x4 * x7 + (-(x5) + x3) * x6 - x3 * x4 = 0)>>;;

time complex_qelim
 <<exists c.
    (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\
    (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\
    (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))>>;;

time complex_qelim
 <<exists b c.
    (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\
    (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\
    (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))>>;;

*********)

time complex_qelim <<forall y.
         a * x^2 + b * x + c = 0 /\
         a * y^2 + b * y + c = 0 /\
         ~(x = y)
         ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

complex_qelim_all
 <<a * x^2 + b * x + c = 0 /\
    a * y^2 + b * y + c = 0 /\
    ~(x = y)
    ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

(* ------------------------------------------------------------------------- *)
(* The Colmerauer example.                                                   *)
(* ------------------------------------------------------------------------- *)

(********* This works, but is quite slow. And it's false! Presumably we
           actually need to use ordering properties associated with absolute
           values

let colmerauer = complex_qelim_all
 <<(x_1 + x_3  = (x_2) \/ x_1 + x_3  = -(x_2)) /\
   (x_2 + x_4  = (x_3) \/ x_2 + x_4  = -(x_3)) /\
   (x_3 + x_5  = (x_4) \/ x_3 + x_5  = -(x_4)) /\
   (x_4 + x_6  = (x_5) \/ x_4 + x_6  = -(x_5)) /\
   (x_5 + x_7  = (x_6) \/ x_5 + x_7  = -(x_6)) /\
   (x_6 + x_8  = (x_7) \/ x_6 + x_8  = -(x_7)) /\
   (x_7 + x_9  = (x_8) \/ x_7 + x_9  = -(x_8)) /\
   (x_8 + x_10 = (x_9) \/ x_8 + x_10 = -(x_9)) /\
   (x_9 + x_11 = (x_10) \/ x_9 + x_11 = -(x_10))
   ==> x_1 = x_10 /\ x_2 = x_11>>;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* Checking resultants from Maple.                                           *)
(* ------------------------------------------------------------------------- *)

(*** interface(prettyprint=0);
     resultant(a * x^2 + b * x + c, 2 * a * x + b,x);
 ***)

time complex_qelim
<<forall a b c.
   (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
   (4*a^2*c-b^2*a = 0)>>;;

time complex_qelim
<<forall a b c d e.
  (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
   a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0>>;;

time complex_qelim
<<forall a b c d e f.
   (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
   (a = 0) /\ (d = 0) <=>
   d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0>>;;

(**** No hope for this one I think

time complex_qelim
<<forall a b c d e f g.
  (exists x. a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0) \/
  (a = 0) /\ (e = 0) <=>
  e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
  g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0>>;;

 ****)

(* ------------------------------------------------------------------------- *)
(* Some trigonometric addition formulas (checking stuff from Maple).         *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
  <<forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1>>;;

(* ------------------------------------------------------------------------- *)
(* The examples from my thesis.                                              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall s c. s^2 + c^2 = 1
      ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3>>;;

time complex_qelim <<forall u v.
  -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
     (((7 * u^6) * v) * v - (u * u^7)) * 144 -
     (((5 * u^4) * v) * v - (u * u^5)) * 168 -
     (((3 * u^2) * v) * v - (u * u^3)) * 210 -
     (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
   (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
   (u^2 + v^2 - 1)>>;;

time complex_qelim <<forall u v.
        u^2 + v^2 = 1
        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
            (v * v - (u * u)) * 315 + 1280 * u^10 = 315>>;;

(* ------------------------------------------------------------------------- *)
(* Deliberately silly examples from Poizat's model theory book (6.6).        *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists z. x * z^87 + y * z^44 + 1 = 0>>;;

time complex_qelim <<forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Actually prove simple equivalences.                                       *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
                  <=> ~(x = 0) \/ ~(y = 0)>>;;

time complex_qelim <<forall x y z. (forall u. exists v.
                         x * (u + v^2)^2 + y * (u + v^2) + z = 0)
                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Invertibility of 2x2 matrix in terms of nonzero determinant.              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists w x y z. (a * w + b * y = 1) /\
                      (a * x + b * z = 0) /\
                      (c * w + d * y = 0) /\
                      (c * x + d * z = 1)>>;;

time complex_qelim <<forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\
                         (a * x + b * z = 0) /\
                         (c * w + d * y = 0) /\
                         (c * x + d * z = 1))
        <=> ~(a * d = b * c)>>;;

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. Not all complex cbrts work.    *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall m n x u t cu ct.
   t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n>>;;

time complex_qelim
 <<forall m n x u t.
   t - u = n /\ 27 * t * u = m^3
   ==> exists ct cu. ct^3 = t /\ cu^3 = u /\
                     (x = ct - cu ==> x^3 + m * x = n)>>;;

(* ------------------------------------------------------------------------- *)
(* SOS in rational functions for Motzkin polynomial (dehomogenized).         *)
(* Of course these are just trivial normalization, nothing deep.             *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
     x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^4 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^4 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    (x^2 * y * (x^2 + y^2 - 2))^2 +
    (x * y^2 * (x^2 + y^2 - 2))^2 +
    (x * y * (x^2 + y^2 - 2))^2 +
    (x^2 - y^2)^2>>;;

(* ------------------------------------------------------------------------- *)
(* A cute bilinear identity -- see ch14 of Rajwade's "Squares" for more.     *)
(* ------------------------------------------------------------------------- *)

polytest
<<|(x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
   (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
    y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
   ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
    (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
    (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
    (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
    (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
    (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
    (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
    (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
    (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
    (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
    (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
    (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
    (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
    (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
    (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
    (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)|>>;;

(* ------------------------------------------------------------------------- *)
(* This is essentially the Cauchy-Riemann conditions for a differential.     *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
  <<forall x y. (a * x + b * y = u * x - v * y) /\
                (c * x + d * y = u * y + v * x)
                ==> (a = d)>>;;

time complex_qelim
  <<forall a b c d.
      (forall x y. (a * x + b * y = u * x - v * y) /\
                   (c * x + d * y = u * y + v * x))
                   ==> (a = d) /\ (b = -(c))>>;;

time complex_qelim
  <<forall a b c d.
        (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\
                                 (c * x + d * y = u * y + v * x))
        <=> (a = d) /\ (b = -(c))>>;;

(* ------------------------------------------------------------------------- *)
(* Finding non-trivial perpendiculars to lines.                              *)
(* ------------------------------------------------------------------------- *)

complex_qelim
  <<forall x1 y1 x2 y2. exists a b.
      ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0>>;;

*)
(* ========================================================================= *)
(* Real quantifier elimination (using Cohen-Hormander algorithm).            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Formal derivative of polynomial.                                          *)
(* ------------------------------------------------------------------------- *)

let rec poly_diffn x n p =
  match p with
    Fn("+",[c; Fn("*",[y; q])]) when y = x ->
        Fn("+",[poly_cmul(Int n) c; Fn("*",[x; poly_diffn x (n+1) q])])
  | _ -> poly_cmul(Int n) p;;

let poly_diff vars p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
         poly_diffn (Var x) 1 q
  | _ -> zero;;

(* ------------------------------------------------------------------------- *)
(* Evaluate a quantifier-free formula given a sign matrix row for its polys. *)
(* ------------------------------------------------------------------------- *)

let rel_signs =
  ["=",[Zero]; "<=",[Zero;Negative]; ">=",[Zero;Positive];
   "<",[Negative]; ">",[Positive]];;

let testform pmat fm =
  eval fm (fun (R(a,[p;z])) -> mem (assoc p pmat) (assoc a rel_signs));;

(* ------------------------------------------------------------------------- *)
(* Infer sign of p(x) at points from corresponding qi(x) with pi(x) = 0      *)
(* ------------------------------------------------------------------------- *)

let inferpsign (pd,qd) =
  try let i = index Zero pd in el i qd :: pd
  with Failure _ -> Nonzero :: pd;;

(* ------------------------------------------------------------------------- *)
(* Condense subdivision by removing points with no relevant zeros.           *)
(* ------------------------------------------------------------------------- *)

let rec condense ps =
  match ps with
    int::pt::other -> let rest = condense other in
                      if mem Zero pt then int::pt::rest else rest
  | _ -> ps;;

(* ------------------------------------------------------------------------- *)
(* Infer sign on intervals (use with infinities at end) and split if needed  *)
(* ------------------------------------------------------------------------- *)

let rec inferisign ps =
  match ps with
    ((l::ls) as x)::(_::ints)::((r::rs)::xs as pts) ->
       (match (l,r) with
          (Zero,Zero) -> failwith "inferisign: inconsistent"
        | (Nonzero,_)
        | (_,Nonzero) -> failwith "inferisign: indeterminate"
        | (Zero,_) -> x::(r::ints)::inferisign pts
        | (_,Zero) -> x::(l::ints)::inferisign pts
        | (Negative,Negative)
        | (Positive,Positive) -> x::(l::ints)::inferisign pts
        | _ -> x::(l::ints)::(Zero::ints)::(r::ints)::inferisign pts)
  | _ -> ps;;

(* ------------------------------------------------------------------------- *)
(* Deduce matrix for p,p1,...,pn from matrix for p',p1,...,pn,q0,...,qn      *)
(* where qi = rem(p,pi) with p0 = p'                                         *)
(* ------------------------------------------------------------------------- *)

let dedmatrix cont mat =
  let l = length (hd mat) / 2 in
  let mat1 = condense(map (inferpsign ** chop_list l) mat) in
  let mat2 = [swap true (el 1 (hd mat1))]::mat1@[[el 1 (last mat1)]] in
  let mat3 = butlast(tl(inferisign mat2)) in
  cont(condense(map (fun l -> hd l :: tl(tl l)) mat3));;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division making sure the remainder has the same sign.              *)
(* ------------------------------------------------------------------------- *)

let pdivide_pos vars sgns s p =
  let a = head vars p and (k,r) = pdivide vars s p in
  let sgn = findsign sgns a in
  if sgn = Zero then failwith "pdivide_pos: zero head coefficient"
  else if sgn = Positive or k mod 2 = 0 then r
  else if sgn = Negative then poly_neg r else poly_mul vars a r;;

(* ------------------------------------------------------------------------- *)
(* Case splitting for positive/negative (assumed nonzero).                   *)
(* ------------------------------------------------------------------------- *)

let split_sign sgns pol cont =
  match findsign sgns pol with
    Nonzero -> let fm = Atom(R(">",[pol; zero])) in
               Or(And(fm,cont(assertsign sgns (pol,Positive))),
                  And(Not fm,cont(assertsign sgns (pol,Negative))))
  | _ -> cont sgns;;

let split_trichotomy sgns pol cont_z cont_pn =
  split_zero sgns pol cont_z (fun s' -> split_sign s' pol cont_pn);;

(* ------------------------------------------------------------------------- *)
(* Main recursive evaluation of sign matrices.                               *)
(* ------------------------------------------------------------------------- *)

let rec casesplit vars dun pols cont sgns =
  match pols with
    [] -> matrix vars dun cont sgns
  | p::ops -> split_trichotomy sgns (head vars p)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars dun (behead vars p :: ops) cont)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars (dun@[p]) ops cont)

and delconst vars dun p ops cont sgns =
  let cont' m = cont(map (insertat (length dun) (findsign sgns p)) m) in
  casesplit vars dun ops cont' sgns

and matrix vars pols cont sgns =
  if pols = [] then try cont [[]] with Failure _ -> False else
  let p = hd(sort(decreasing (degree vars)) pols) in
  let p' = poly_diff vars p and i = index p pols in
  let qs = let p1,p2 = chop_list i pols in p'::p1 @ tl p2 in
  let gs = map (pdivide_pos vars sgns p) qs in
  let cont' m = cont(map (fun l -> insertat i (hd l) (tl l)) m) in
  casesplit vars [] (qs@gs) (dedmatrix cont') sgns;;

(* ------------------------------------------------------------------------- *)
(* Now the actual quantifier elimination code.                               *)
(* ------------------------------------------------------------------------- *)

let basic_real_qelim vars (Exists(x,p)) =
  let pols = atom_union
    (function (R(a,[t;Fn("0",[])])) -> [t] | _ -> []) p in
  let cont mat = if exists (fun m -> testform (zip pols m) p) mat
                 then True else False in
  casesplit (x::vars) [] pols cont init_sgns;;

let real_qelim =
  simplify ** evalc **
  lift_qelim polyatom (simplify ** evalc) basic_real_qelim;;

(* ------------------------------------------------------------------------- *)
(* First examples.                                                           *)
(* ------------------------------------------------------------------------- *)

(*
real_qelim <<exists x. x^4 + x^2 + 1 = 0>>;;

real_qelim <<exists x. x^3 - x^2 + x - 1 = 0>>;;

real_qelim <<exists x y. x^3 - x^2 + x - 1 = 0 /\
                         y^3 - y^2 + y - 1 = 0 /\ ~(x = y)>>;;

#trace testform;;
real_qelim <<exists x. x^2 - 3 * x + 2 = 0 /\ 2 * x - 3 = 0>>;;
#untrace testform;;

real_qelim
 <<forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k>>;;

real_qelim <<exists x. a * x^2 + b * x + c = 0>>;;

real_qelim <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           b^2 >= 4 * a * c>>;;

real_qelim <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                           a = 0 /\ (b = 0 ==> c = 0) \/
                           ~(a = 0) /\ b^2 >= 4 * a * c>>;;

(* ------------------------------------------------------------------------- *)
(* Termination ordering for group theory completion.                         *)
(* ------------------------------------------------------------------------- *)

real_qelim <<1 < 2 /\ (forall x. 1 < x ==> 1 < x^2) /\
             (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))>>;;
*)

let rec grpterm tm =
  match tm with
    Fn("*",[s;t]) -> let t2 = Fn("*",[Fn("2",[]); grpterm t]) in
                     Fn("*",[grpterm s; Fn("+",[Fn("1",[]); t2])])
  | Fn("i",[t]) -> Fn("^",[grpterm t; Fn("2",[])])
  | Fn("1",[]) -> Fn("2",[])
  | Var x -> tm;;

let grpform (Atom(R("=",[s;t]))) =
  let fm = generalize(Atom(R(">",[grpterm s; grpterm t]))) in
  relativize(fun x -> Atom(R(">",[Var x;Fn("1",[])]))) fm;;

(*
let eqs = complete_and_simplify ["1"; "*"; "i"]
  [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

let fm = list_conj (map grpform eqs);;

real_qelim fm;;
*)

(* ------------------------------------------------------------------------- *)
(* A case where using DNF is an improvement.                                 *)
(* ------------------------------------------------------------------------- *)

let real_qelim' =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
                      basic_real_qelim;;

real_qelim'
 <<forall d.
     (exists c. forall a b. (a = d /\ b = c) \/ (a = c /\ b = 1)
                            ==> a^2 = b)
     <=> d^4 = 1>>;;

(* ------------------------------------------------------------------------- *)
(* Didn't seem worth it in the book, but monicization can help a lot.        *)
(* Now this is just set as an exercise.                                      *)
(* ------------------------------------------------------------------------- *)

(*
let rec casesplit vars dun pols cont sgns =
  match pols with
    [] -> monicize vars dun cont sgns
  | p::ops -> split_trichotomy sgns (head vars p)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars dun (behead vars p :: ops) cont)
                (if is_constant vars p then delconst vars dun p ops cont
                 else casesplit vars (dun@[p]) ops cont)

and delconst vars dun p ops cont sgns =
  let cont' m = cont(map (insertat (length dun) (findsign sgns p)) m) in
  casesplit vars dun ops cont' sgns

and matrix vars pols cont sgns =
  if pols = [] then try cont [[]] with Failure _ -> False else
  let p = hd(sort(decreasing (degree vars)) pols) in
  let p' = poly_diff vars p and i = index p pols in
  let qs = let p1,p2 = chop_list i pols in p'::p1 @ tl p2 in
  let gs = map (pdivide_pos vars sgns p) qs in
  let cont' m = cont(map (fun l -> insertat i (hd l) (tl l)) m) in
  casesplit vars [] (qs@gs) (dedmatrix cont') sgns

and monicize vars pols cont sgns =
  let mols,swaps = unzip(map monic pols) in
  let sols = setify mols in
  let indices = map (fun p -> index p sols) mols in
  let transform m =
    map2 (fun sw i -> swap sw (el i m)) swaps indices in
  let cont' mat = cont(map transform mat) in
  matrix vars sols cont' sgns;;

let basic_real_qelim vars (Exists(x,p)) =
  let pols = atom_union
    (function (R(a,[t;Fn("0",[])])) -> [t] | _ -> []) p in
  let cont mat = if exists (fun m -> testform (zip pols m) p) mat
                 then True else False in
  casesplit (x::vars) [] pols cont init_sgns;;

let real_qelim =
  simplify ** evalc **
  lift_qelim polyatom (simplify ** evalc) basic_real_qelim;;

let real_qelim' =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
                      basic_real_qelim;;
*)
(* ========================================================================= *)
(* Grobner basis algorithm.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul (c1,m1) (c2,m2) = (c1*/c2,map2 (+) m1 m2);;

let mdiv =
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun (c1,m1) (c2,m2) -> (c1//c2,map2 index_sub m1 m2);;

let mlcm (c1,m1) (c2,m2) = (Int 1,map2 max m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 or n1 = n2 & lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_mmul cm pol = map (mmul cm) pol;;

let mpoly_neg = map (fun (c,m) -> (minus_num c,m));;

let mpoly_const vars c =
  if c =/ Int 0 then [] else [c,map (fun k -> 0) vars];;

let mpoly_var vars x =
  [Int 1,map (fun y -> if y = x then 1 else 0) vars];;

let rec mpoly_add l1 l2 =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = mpoly_add o1 o2 in
          if c =/ Int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(mpoly_add o1 l2)
        else (c2,m2)::(mpoly_add l1 o2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

let rec mpoly_mul l1 l2 =
  match l1 with
    [] -> []
  | (h1::t1) -> mpoly_add (mpoly_mmul h1 l2) (mpoly_mul t1 l2);;

let mpoly_pow vars l n =
  funpow n (mpoly_mul l) (mpoly_const vars (Int 1));;

let mpoly_inv p =
  match p with 
    [(c,m)] when forall (fun i -> i = 0) m -> [(Int 1 // c),m]
  | _ -> failwith "mpoly_inv: non-constant polynomial";;

let mpoly_div p q = mpoly_mul p (mpoly_inv q);;

(* ------------------------------------------------------------------------- *)
(* Convert formula into canonical form.                                      *)
(* ------------------------------------------------------------------------- *)

let rec mpolynate vars tm =
  match tm with
    Var x -> mpoly_var vars x
  | Fn("-",[t]) -> mpoly_neg (mpolynate vars t)
  | Fn("+",[s;t]) -> mpoly_add (mpolynate vars s) (mpolynate vars t)
  | Fn("-",[s;t]) -> mpoly_sub (mpolynate vars s) (mpolynate vars t)
  | Fn("*",[s;t]) -> mpoly_mul (mpolynate vars s) (mpolynate vars t)
  | Fn("/",[s;t]) -> mpoly_div (mpolynate vars s) (mpolynate vars t)
  | Fn("^",[t;Fn(n,[])]) ->
                mpoly_pow vars (mpolynate vars t) (int_of_string n)
  | _ -> mpoly_const vars (dest_numeral tm);;

let mpolyatom vars fm =
  match fm with
    Atom(R("=",[s;t])) -> mpolynate vars (Fn("-",[s;t]))
  | _ -> failwith "mpolyatom: not an equation";;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 cm pol =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv cm hm in mpoly_mmul (minus_num c,m) cms;;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb cm pols = tryfind (reduce1 cm) pols;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce pols pol =
  match pol with
    [] -> []
  | cm::ptl -> try reduce pols (mpoly_add (reduceb cm pols) ptl)
               with Failure _ -> cm::(reduce pols ptl);;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly pol1 pol2 =
  match (pol1,pol2) with
    ([],p) -> []
  | (p,[]) -> []
  | (m1::ptl1,m2::ptl2) ->
        let m = mlcm m1 m2 in
        mpoly_sub (mpoly_mmul (mdiv m m1) ptl1)
                  (mpoly_mmul (mdiv m m2) ptl2);;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec grobner basis pairs =
  print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" pairs");
  print_newline();
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
        let sp = reduce basis (spoly p1 p2) in
        if sp = [] then grobner basis opairs
        else if forall (forall ((=) 0) ** snd) sp then [sp] else
        let newcps = map (fun p -> p,sp) basis in
        grobner (sp::basis) (opairs @ newcps);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner basis = grobner basis (distinctpairs basis);;

(* ------------------------------------------------------------------------- *)
(* Use the Rabinowitsch trick to eliminate inequations.                      *)
(* That is, replace p =/= 0 by exists v. 1 - v * p = 0                       *)
(* ------------------------------------------------------------------------- *)

let rabinowitsch vars v p =
   mpoly_sub (mpoly_const vars (Int 1))
             (mpoly_mul (mpoly_var vars v) p);;

(* ------------------------------------------------------------------------- *)
(* Universal complex number decision procedure based on Grobner bases.       *)
(* ------------------------------------------------------------------------- *)

let grobner_trivial fms =
  let vars0 = itlist (union ** fv) fms []
  and eqs,neqs = partition positive fms in
  let rvs = map (fun n -> variant ("_"^string_of_int n) vars0)
                (1--length neqs) in
  let vars = vars0 @ rvs in
  let poleqs = map (mpolyatom vars) eqs
  and polneqs = map (mpolyatom vars ** negate) neqs in
  let pols = poleqs @ map2 (rabinowitsch vars) rvs polneqs in
  reduce (groebner pols) (mpoly_const vars (Int 1)) = [];;

let grobner_decide fm =
  let fm1 = specialize(prenex(nnf(simplify fm))) in
  forall grobner_trivial (simpdnf(nnf(Not fm1)));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
grobner_decide
  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

grobner_decide
  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

grobner_decide
  <<(a * x^2 + b * x + c = 0) /\
   (a * y^2 + b * y + c = 0) /\
   ~(x = y)
   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

(* ------------------------------------------------------------------------- *)
(* Compare with earlier procedure.                                           *)
(* ------------------------------------------------------------------------- *)

let fm =
  <<(a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>> in
time complex_qelim (generalize fm),time grobner_decide fm;;

(* ------------------------------------------------------------------------- *)
(* More tests.                                                               *)
(* ------------------------------------------------------------------------- *)

time grobner_decide  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

time grobner_decide  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

time grobner_decide <<(a * x^2 + b * x + c = 0) /\
      (a * y^2 + b * y + c = 0) /\
      ~(x = y)
      ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time grobner_decide
 <<(y_1 = 2 * y_3) /\
  (y_2 = 2 * y_4) /\
  (y_1 * y_3 = y_2 * y_4)
  ==> (y_1^2 = y_2^2)>>;;

time grobner_decide
 <<(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)>>;;

time grobner_decide
 <<(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)>>;;

(*** Checking resultants (in one direction) ***)

time grobner_decide
<<a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0
 ==> 4*a^2*c-b^2*a = 0>>;;

time grobner_decide
<<a * x^2 + b * x + c = 0 /\ d * x + e = 0
 ==> d^2*c-e*d*b+a*e^2 = 0>>;;


time grobner_decide
<<a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
 ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0>>;;

(****** Seems a bit too lengthy?

time grobner_decide
<<a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
 ==>
e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0>>;;

 ********)

(********** Works correctly, but it's lengthy

time grobner_decide
 << (x1 - x0)^2 + (y1 - y0)^2 =
   (x2 - x0)^2 + (y2 - y0)^2 /\
   (x2 - x0)^2 + (y2 - y0)^2 =
   (x3 - x0)^2 + (y3 - y0)^2 /\
   (x1 - x0')^2 + (y1 - y0')^2 =
   (x2 - x0')^2 + (y2 - y0')^2 /\
   (x2 - x0')^2 + (y2 - y0')^2 =
   (x3 - x0')^2 + (y3 - y0')^2
   ==> x0 = x0' /\ y0 = y0'>>;;

       **** Corrected with non-isotropy conditions; even lengthier

time grobner_decide
 <<(x1 - x0)^2 + (y1 - y0)^2 =
  (x2 - x0)^2 + (y2 - y0)^2 /\
  (x2 - x0)^2 + (y2 - y0)^2 =
  (x3 - x0)^2 + (y3 - y0)^2 /\
  (x1 - x0')^2 + (y1 - y0')^2 =
  (x2 - x0')^2 + (y2 - y0')^2 /\
  (x2 - x0')^2 + (y2 - y0')^2 =
  (x3 - x0')^2 + (y3 - y0')^2 /\
  ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\
  ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
  ==> x0 = x0' /\ y0 = y0'>>;;

        *** Maybe this is more efficient? (No?)

time grobner_decide
 <<(x1 - x0)^2 + (y1 - y0)^2 = d /\
  (x2 - x0)^2 + (y2 - y0)^2 = d /\
  (x3 - x0)^2 + (y3 - y0)^2 = d /\
  (x1 - x0')^2 + (y1 - y0')^2 = e /\
  (x2 - x0')^2 + (y2 - y0')^2 = e /\
  (x3 - x0')^2 + (y3 - y0')^2 = e /\
  ~(d = 0) /\ ~(e = 0)
  ==> x0 = x0' /\ y0 = y0'>>;;

***********)

(* ------------------------------------------------------------------------- *)
(* Inversion of homographic function (from Gosper's CF notes).               *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y>>;;

(* ------------------------------------------------------------------------- *)
(* Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall a b c d e.
     a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
     ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0>>;;

time grobner_decide
  <<a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
    ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0>>;;

(* ------------------------------------------------------------------------- *)
(* Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall b d e.
     b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
     ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0>>;;

time grobner_decide
  <<b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
    ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0>>;;

(* ------------------------------------------------------------------------- *)
(* Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 *)
(*                                                                           *)
(* This derives b <= 0, but not a full solution.                             *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Here are further steps towards a solution, step-by-step.                  *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)>>;;

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3>>;;

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                *)
(*                                                                           *)
(* Yet even this isn't completed!                                            *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. This actually works worse than *)
(* with naive quantifier elimination (of course it's false...)               *)
(* ------------------------------------------------------------------------- *)

(******

time grobner_decide
 <<t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n>>;;

***********)

*)

(* ------------------------------------------------------------------------- *)
(* For looking at things it's nice to map back to normal term.               *)
(* ------------------------------------------------------------------------- *)

(*****

let term_of_varpow vars (x,k) =
  if k = 1 then Var x else Fn("^",[Var x; mk_numeral(Int k)]);;

let term_of_varpows vars lis =
  let tms = filter (fun (a,b) -> b <> 0) (zip vars lis) in
  end_itlist (fun s t -> Fn("*",[s;t])) (map (term_of_varpow vars) tms);;

let term_of_monomial vars (c,m) =
  if forall (fun x -> x = 0) m then mk_numeral c
  else if c =/ Int 1 then term_of_varpows vars m
  else Fn("*",[mk_numeral c; term_of_varpows vars m]);;

let term_of_poly vars pol =
  end_itlist (fun s t -> Fn("+",[s;t])) (map (term_of_monomial vars) pol);;

let grobner_basis vars pols =
  map (term_of_poly vars) (groebner (map (mpolyatom vars) pols));;

*****)
(* ========================================================================= *)
(* Geometry theorem proving.                                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* List of geometric properties with their coordinate translations.          *)
(* ------------------------------------------------------------------------- *)

let coordinations =
  ["collinear", (** Points 1, 2 and 3 lie on a common line **)
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)>>;
   "parallel", (** Lines (1,2) and (3,4) are parallel **)
    <<(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)>>;
   "perpendicular", (** Lines (1,2) and (3,4) are perpendicular **)
   <<(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0>>;
   "lengths_eq", (** Lines (1,2) and (3,4) have the same length **)
   <<(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2>>;
   "is_midpoint", (** Point 1 is the midpoint of line (2,3) **)
   <<2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y>>;
   "is_intersection", (** Lines (2,3) and (4,5) meet at point 1 **)
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\
     (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)>>;
   "=", (** Points 1 and 2 are the same **)
   <<(1_x = 2_x) /\ (1_y = 2_y)>>];;

(* ------------------------------------------------------------------------- *)
(* Convert formula into coordinate form.                                     *)
(* ------------------------------------------------------------------------- *)

let coordinate = onatoms
  (fun (R(a,args)) ->
    let xtms,ytms = unzip
     (map (fun (Var v) -> Var(v^"_x"),Var(v^"_y")) args) in
    let xs = map (fun n -> string_of_int n^"_x") (1--length args)
    and ys = map (fun n -> string_of_int n^"_y") (1--length args) in
    subst (fpf (xs @ ys) (xtms @ ytms)) (assoc a coordinations));;

(* ------------------------------------------------------------------------- *)
(* Trivial example.                                                          *)
(* ------------------------------------------------------------------------- *)

(*
coordinate <<collinear(a,b,c) ==> collinear(b,a,c)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Verify equivalence under rotation.                                        *)
(* ------------------------------------------------------------------------- *)

let invariant (x',y') ((s:string),z) =
  let m n f =
    let x = string_of_int n^"_x" and y = string_of_int n^"_y" in
    let i = fpf ["x";"y"] [Var x;Var y] in
    (x |-> tsubst i x') ((y |-> tsubst i y') f) in
  Iff(z,subst(itlist m (1--5) undefined) z);;

let invariant_under_translation = invariant (<<|x + X|>>,<<|y + Y|>>);;

(*
forall (grobner_decide ** invariant_under_translation) coordinations;;
*)

let invariant_under_rotation fm =
  Imp(<<s^2 + c^2 = 1>>,
      invariant (<<|c * x - s * y|>>,<<|s * x + c * y|>>) fm);;

(*
forall (grobner_decide ** invariant_under_rotation) coordinations;;
*)

(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)

(*
real_qelim
 <<forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Choose one point to be the origin and rotate to zero another y coordinate *)
(* ------------------------------------------------------------------------- *)

let originate fm =
  let a::b::ovs = fv fm in
  subst (fpf [a^"_x"; a^"_y"; b^"_y"] [zero; zero; zero])
        (coordinate fm);;

(* ------------------------------------------------------------------------- *)
(* Other interesting invariances.                                            *)
(* ------------------------------------------------------------------------- *)

let invariant_under_scaling fm =
  Imp(<<~(A = 0)>>,invariant(<<|A * x|>>,<<|A * y|>>) fm);;

let invariant_under_shearing = invariant(<<|x + b * y|>>,<<|y|>>);;

(*
forall (grobner_decide ** invariant_under_scaling) coordinations;;

partition (grobner_decide ** invariant_under_shearing) coordinations;;
*)

(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)

(*
(grobner_decide ** originate)
 <<is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
   ==> lengths_eq(a,b,b,c)>>;;

(* ------------------------------------------------------------------------- *)
(* Parallelogram theorem (Chou's expository example at the start).           *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d)
   ==> lengths_eq(a,e,e,c)>>;;

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
   ==> lengths_eq(a,e,e,c)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Reduce p using triangular set, collecting degenerate conditions.          *)
(* ------------------------------------------------------------------------- *)

let rec pprove vars triang p degens =
  if p = zero then degens else
  match triang with
    [] -> (mk_eq p zero)::degens
  | (Fn("+",[c;Fn("*",[Var x;_])]) as q)::qs ->
        if x <> hd vars then
          if mem (hd vars) (fvt p)
          then itlist (pprove vars triang) (coefficients vars p) degens
          else pprove (tl vars) triang p degens
        else
          let k,p' = pdivide vars p q in
          if k = 0 then pprove vars qs p' degens else
          let degens' = Not(mk_eq (head vars q) zero)::degens in
          itlist (pprove vars qs) (coefficients vars p') degens';;

(* ------------------------------------------------------------------------- *)
(* Triangulate a set of polynomials.                                         *)
(* ------------------------------------------------------------------------- *)

let rec triangulate vars consts pols =
  if vars = [] then pols else
  let cns,tpols = partition (is_constant vars) pols in
  if cns <> [] then triangulate vars (cns @ consts) tpols else
  if length pols <= 1 then pols @ triangulate (tl vars) [] consts else
  let n = end_itlist min (map (degree vars) pols) in
  let p = find (fun p -> degree vars p = n) pols in
  let ps = subtract pols [p] in
  triangulate vars consts (p::map (fun q -> snd(pdivide vars q p)) ps);;

(* ------------------------------------------------------------------------- *)
(* Trivial version of Wu's method based on repeated pseudo-division.         *)
(* ------------------------------------------------------------------------- *)

let wu fm vars zeros =
  let gfm0 = coordinate fm in
  let gfm = subst(itlist (fun v -> v |-> zero) zeros undefined) gfm0 in
  if not (set_eq vars (fv gfm)) then failwith "wu: bad parameters" else
  let ant,con = dest_imp gfm in
  let pols = map (lhs ** polyatom vars) (conjuncts ant)
  and ps = map (lhs ** polyatom vars) (conjuncts con) in
  let tri = triangulate vars [] pols in
  itlist (fun p -> union(pprove vars tri p [])) ps [];;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

(*
let simson =
 <<lengths_eq(o,a,o,b) /\
   lengths_eq(o,a,o,c) /\
   lengths_eq(o,a,o,d) /\
   collinear(e,b,c) /\
   collinear(f,a,c) /\
   collinear(g,a,b) /\
   perpendicular(b,c,d,e) /\
   perpendicular(a,c,d,f) /\
   perpendicular(a,b,d,g)
   ==> collinear(e,f,g)>>;;

let vars =
 ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
  "b_y"; "b_x"; "o_x"]
and zeros = ["a_x"; "a_y"; "o_y"];;

wu simson vars zeros;;

(* ------------------------------------------------------------------------- *)
(* Try without special coordinates.                                          *)
(* ------------------------------------------------------------------------- *)

wu simson (vars @ zeros) [];;

(* ------------------------------------------------------------------------- *)
(* Pappus (Chou's figure 6).                                                 *)
(* ------------------------------------------------------------------------- *)

let pappus =
 <<collinear(a1,b2,d) /\
   collinear(a2,b1,d) /\
   collinear(a2,b3,e) /\
   collinear(a3,b2,e) /\
   collinear(a1,b3,f) /\
   collinear(a3,b1,f)
   ==> collinear(d,e,f)>>;;

let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
            "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

wu pappus vars zeros;;

(* ------------------------------------------------------------------------- *)
(* The Butterfly (figure 9).                                                 *)
(* ------------------------------------------------------------------------- *)

(****
let butterfly =
 <<lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\
   collinear(a,e,c) /\ collinear(d,e,b) /\
   perpendicular(e,f,o,e) /\
   collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g)
   ==> is_midpoint(e,f,g)>>;;

let vars = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y";
            "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]
and zeros = ["a_y"; "o_x"; "o_y"];;

 **** This one is costly (too big for laptop, but doable in about 300M)
 **** However, it gives exactly the same degenerate conditions as Chou

wu butterfly vars zeros;;

 ****
 ****)
*)

(*** Other examples removed from text

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
   is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d)
   ==> collinear(c,f,m)>>;;

****)
(* ========================================================================= *)
(* Implementation/proof of the Craig-Robinson interpolation theorem.         *)
(*                                                                           *)
(* This is based on the proof in Kreisel & Krivine, which works very nicely  *)
(* in our context.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpolation for propositional logic.                                    *)
(* ------------------------------------------------------------------------- *)

let pinterpolate p q =
  let orify a r = Or(psubst(a|=>False) r,psubst(a|=>True) r) in
  psimplify(itlist orify (subtract (atoms p) (atoms q)) p);;

(* ------------------------------------------------------------------------- *)
(* Relation-symbol interpolation for universal closed formulas.              *)
(* ------------------------------------------------------------------------- *)

let urinterpolate p q =
  let fm = specialize(prenex(And(p,q))) in
  let fvs = fv fm and consts,funcs = herbfuns fm in
  let cntms = map (fun (c,_) -> Fn(c,[])) consts in
  let tups = dp_refine_loop (simpcnf fm) cntms funcs fvs 0 [] [] [] in
  let fmis = map (fun tup -> subst (fpf fvs tup) fm) tups in
  let ps,qs = unzip (map (fun (And(p,q)) -> p,q) fmis) in
  pinterpolate (list_conj(setify ps)) (list_conj(setify qs));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let p = prenex
 <<(forall x. R(x,f(x))) /\ (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))>>
and q = prenex
 <<(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(0,0)>>;;

let c = urinterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;
*)

(* ------------------------------------------------------------------------- *)
(* Pick the topmost terms starting with one of the given function symbols.   *)
(* ------------------------------------------------------------------------- *)

let rec toptermt fns tm =
  match tm with
    Var x -> []
  | Fn(f,args) -> if mem (f,length args) fns then [tm]
                  else itlist (union ** toptermt fns) args [];;

let topterms fns = atom_union
  (fun (R(p,args)) -> itlist (union ** toptermt fns) args []);;

(* ------------------------------------------------------------------------- *)
(* Interpolation for arbitrary universal formulas.                           *)
(* ------------------------------------------------------------------------- *)

let uinterpolate p q =
  let fp = functions p and fq = functions q in
  let rec simpinter tms n c =
    match tms with
      [] -> c
    | (Fn(f,args) as tm)::otms ->
        let v = "v_"^(string_of_int n) in
        let c' = replace (tm |=> Var v) c in
        let c'' = if mem (f,length args) fp
                  then Exists(v,c') else Forall(v,c') in
        simpinter otms (n+1) c'' in
  let c = urinterpolate p q in
  let tts = topterms (union (subtract fp fq) (subtract fq fp)) c in
  let tms = sort (decreasing termsize) tts in
  simpinter tms 1 c;;

(* ------------------------------------------------------------------------- *)
(* The same example now gives a true interpolant.                            *)
(* ------------------------------------------------------------------------- *)

(*
let c = uinterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;
*)

(* ------------------------------------------------------------------------- *)
(* Now lift to arbitrary formulas with no common free variables.             *)
(* ------------------------------------------------------------------------- *)

let cinterpolate p q =
  let fm = nnf(And(p,q)) in
  let efm = itlist mk_exists (fv fm) fm
  and fns = map fst (functions fm) in
  let And(p',q'),_ = skolem efm fns in
  uinterpolate p' q';;

(* ------------------------------------------------------------------------- *)
(* Now to completely arbitrary formulas.                                     *)
(* ------------------------------------------------------------------------- *)

let interpolate p q =
  let vs = map (fun v -> Var v) (intersect (fv p) (fv q))
  and fns = functions (And(p,q)) in
  let n = itlist (max_varindex "c_" ** fst) fns (Int 0) +/ Int 1 in
  let cs = map (fun i -> Fn("c_"^(string_of_num i),[]))
               (n---(n+/Int(length vs-1))) in
  let fn_vc = fpf vs cs and fn_cv = fpf cs vs in
  let p' = replace fn_vc p and q' = replace fn_vc q in
  replace fn_cv (cinterpolate p' q');;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
let p =
 <<(forall x. exists y. R(x,y)) /\
   (forall x y. S(v,x,y) <=> R(x,y) \/ R(y,x))>>
and q =
 <<(forall x y z. S(v,x,y) /\ S(v,y,z) ==> T(x,z)) /\
   (exists u. ~T(u,u))>>;;

let c = interpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;
*)

(* ------------------------------------------------------------------------- *)
(* Lift to logic with equality.                                              *)
(* ------------------------------------------------------------------------- *)

let einterpolate p q =
  let p' = equalitize p and q' = equalitize q in
  let p'' = if p' = p then p else And(fst(dest_imp p'),p)
  and q'' = if q' = q then q else And(fst(dest_imp q'),q) in
  interpolate p'' q'';;

(* ------------------------------------------------------------------------- *)
(* More examples, not in the text.                                           *)
(* ------------------------------------------------------------------------- *)

(*
let p = <<(p ==> q /\ r)>>
and q = <<~((q ==> p) ==> s ==> (p <=> q))>>;;

let c = interpolate p q;;

tautology(Imp(And(p,q),False));;

tautology(Imp(p,c));;
tautology(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* A more interesting example.                                               *)
(* ------------------------------------------------------------------------- *)

let p = <<(forall x. exists y. R(x,y)) /\
          (forall x y. S(x,y) <=> R(x,y) \/ R(y,x))>>
and q = <<(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)>>;;

meson(Imp(And(p,q),False));;

let c = interpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* A variant where u is free in both parts.                                  *)
(* ------------------------------------------------------------------------- *)

let p = <<(forall x. exists y. R(x,y)) /\
          (forall x y. S(x,y) <=> R(x,y) \/ R(y,x)) /\
          (forall v. R(u,v) ==> Q(v,u))>>
and q = <<(forall x y z. S(x,y) /\ S(y,z) ==> T(x,z)) /\ ~T(u,u)>>;;

meson(Imp(And(p,q),False));;

let c = interpolate p q;;
meson(Imp(p,c));;
meson(Imp(q,Not c));;

(* ------------------------------------------------------------------------- *)
(* Way of generating examples quite easily (see K&K exercises).              *)
(* ------------------------------------------------------------------------- *)

let test_interp fm =
  let p = generalize(skolemize fm)
  and q = generalize(skolemize(Not fm)) in
  let c = interpolate p q in
  meson(Imp(And(p,q),False)); meson(Imp(p,c)); meson(Imp(q,Not c)); c;;

test_interp <<forall x. P(x) ==> exists y. forall z. P(z) ==> Q(y)>>;;

test_interp <<forall y. exists y. forall z. exists a.
                P(a,x,y,z) ==> P(x,y,z,a)>>;;

(* ------------------------------------------------------------------------- *)
(* Hintikka's examples.                                                      *)
(* ------------------------------------------------------------------------- *)

let p = <<forall x. L(x,b)>>
and q = <<(forall y. L(b,y) ==> m = y) /\ ~(m = b)>>;;

let c = einterpolate p q;;

meson(Imp(p,c));;
meson(Imp(q,Not c));;

let p =
 <<(forall x. A(x) /\ C(x) ==> B(x)) /\ (forall x. D(x) \/ ~D(x) ==> C(x))>>
and q =
 <<~(forall x. E(x) ==> A(x) ==> B(x))>>;;

let c = interpolate p q;;
meson(Imp(p,c));;
meson(Imp(q,Not c));;
*)
(* ========================================================================= *)
(* Nelson-Oppen combined decision procedure.                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Real language with decision procedure.                                    *)
(* ------------------------------------------------------------------------- *)

let real_lang =
  let fn = ["-",1; "+",2; "-",2; "*",2; "^",2]
  and pr = ["<=",2; "<",2; ">=",2; ">",2] in
  (fun (s,n) -> n = 0 & is_numeral(Fn(s,[])) or mem (s,n) fn),
  (fun sn -> mem sn pr),
  (fun fm -> real_qelim(generalize fm) = True);;

(* ------------------------------------------------------------------------- *)
(* Integer language with decision procedure.                                 *)
(* ------------------------------------------------------------------------- *)

let int_lang =
  let fn = ["-",1; "+",2; "-",2; "*",2]
  and pr = ["<=",2; "<",2; ">=",2; ">",2] in
  (fun (s,n) -> n = 0 & is_numeral(Fn(s,[])) or mem (s,n) fn),
  (fun sn -> mem sn pr),
  (fun fm -> integer_qelim(generalize fm) = True);;

(* ------------------------------------------------------------------------- *)
(* Add any uninterpreted functions to a list of languages.                   *)
(* ------------------------------------------------------------------------- *)

let add_default langs =
  langs @ [(fun sn -> not (exists (fun (f,p,d) -> f sn) langs)),
           (fun sn -> sn = ("=",2)),ccvalid];;

(* ------------------------------------------------------------------------- *)
(* Choose a language for homogenization of an atom.                          *)
(* ------------------------------------------------------------------------- *)

let chooselang langs fm =
  match fm with
    Atom(R("=",[Fn(f,args);_])) | Atom(R("=",[_;Fn(f,args)])) ->
        find (fun (fn,pr,dp) -> fn(f,length args)) langs
  | Atom(R(p,args)) ->
        find (fun (fn,pr,dp) -> pr(p,length args)) langs;;

(* ------------------------------------------------------------------------- *)
(* General listification for CPS-style function.                             *)
(* ------------------------------------------------------------------------- *)

let rec listify f l cont =
  match l with
    [] -> cont []
  | h::t -> f h (fun h' -> listify f t (fun t' -> cont(h'::t')));;

(* ------------------------------------------------------------------------- *)
(* Homogenize a term.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec homot (fn,pr,dp) tm cont n defs =
  match tm with
    Var x -> cont tm n defs
  | Fn(f,args) ->
       if fn(f,length args) then
       listify (homot (fn,pr,dp)) args (fun a -> cont (Fn(f,a))) n defs
       else cont (Var("v_"^(string_of_num n))) (n +/ Int 1)
                 (mk_eq (Var("v_"^(string_of_num n))) tm :: defs);;

(* ------------------------------------------------------------------------- *)
(* Homogenize a literal.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec homol langs fm cont n defs =
  match fm with
    Not(f) -> homol langs f (fun p -> cont(Not(p))) n defs
  | Atom(R(p,args)) ->
        let lang = chooselang langs fm in
        listify (homot lang) args (fun a -> cont (Atom(R(p,a)))) n defs
  | _ -> failwith "homol: not a literal";;

(* ------------------------------------------------------------------------- *)
(* Fully homogenize a list of literals.                                      *)
(* ------------------------------------------------------------------------- *)

let rec homo langs fms cont =
  listify (homol langs) fms
          (fun dun n defs ->
              if defs = [] then cont dun n defs
              else homo langs defs (fun res -> cont (dun@res)) n []);;

(* ------------------------------------------------------------------------- *)
(* Overall homogenization.                                                   *)
(* ------------------------------------------------------------------------- *)

let homogenize langs fms =
  let fvs = unions(map fv fms) in
  let n = Int 1 +/ itlist (max_varindex "v_") fvs (Int 0) in
  homo langs fms (fun res n defs -> res) n [];;

(* ------------------------------------------------------------------------- *)
(* Whether a formula belongs to a language.                                  *)
(* ------------------------------------------------------------------------- *)

let belongs (fn,pr,dp) fm =
  forall fn (functions fm) &
  forall pr (subtract (predicates fm) ["=",2]);;

(* ------------------------------------------------------------------------- *)
(* Partition formulas among a list of languages.                             *)
(* ------------------------------------------------------------------------- *)

let rec langpartition langs fms =
  match langs with
    [] -> if fms = [] then [] else failwith "langpartition"
  | l::ls -> let fms1,fms2 = partition (belongs l) fms in
             fms1::langpartition ls fms2;;

(* ------------------------------------------------------------------------- *)
(* Running example if we magically knew the interpolant.                     *)
(* ------------------------------------------------------------------------- *)

(*
(integer_qelim ** generalize)
  <<(u + 1 = v /\ v_1 + 1 = u - 1 /\ v_2 - 1 = v + 1 /\ v_3 = v - 1)
    ==> u = v_3 /\ ~(v_1 = v_2)>>;;

ccvalid
  <<(v_2 = f(v_3) /\ v_1 = f(u)) ==> ~(u = v_3 /\ ~(v_1 = v_2))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Turn an arrangement (partition) of variables into corresponding formula.  *)
(* ------------------------------------------------------------------------- *)

let rec arreq l =
  match l with
    v1::v2::rest -> mk_eq (Var v1) (Var v2) :: (arreq (v2::rest))
  | _ -> [];;

let arrangement part =
  itlist (union ** arreq) part
         (map (fun (v,w) -> Not(mk_eq (Var v) (Var w)))
              (distinctpairs (map hd part)));;

(* ------------------------------------------------------------------------- *)
(* Attempt to substitute with trivial equations.                             *)
(* ------------------------------------------------------------------------- *)

let dest_def fm =
  match fm with
    Atom(R("=",[Var x;t])) when not(mem x (fvt t)) -> x,t
  | Atom(R("=",[t; Var x])) when not(mem x (fvt t)) -> x,t
  | _ -> failwith "dest_def";;

let rec redeqs eqs =
  try let eq = find (can dest_def) eqs in
      let x,t = dest_def eq in
      redeqs (map (subst (x |=> t)) (subtract eqs [eq]))
  with Failure _ -> eqs;;

(* ------------------------------------------------------------------------- *)
(* Naive Nelson-Oppen variant trying all arrangements.                       *)
(* ------------------------------------------------------------------------- *)

let trydps ldseps fms =
  exists (fun ((_,_,dp),fms0) -> dp(Not(list_conj(redeqs(fms0 @ fms)))))
         ldseps;;

let allpartitions =
  let allinsertions x l acc =
    itlist (fun p acc -> ((x::p)::(subtract l [p])) :: acc) l
           (([x]::l)::acc) in
  fun l -> itlist (fun h y -> itlist (allinsertions h) y []) l [[]];;

let nelop_refute vars ldseps =
  forall (trydps ldseps ** arrangement) (allpartitions vars);;

let nelop1 langs fms0 =
  let fms = homogenize langs fms0 in
  let seps = langpartition langs fms in
  let fvlist = map (unions ** map fv) seps in
  let vars = filter (fun x -> length (filter (mem x) fvlist) >= 2)
                    (unions fvlist) in
  nelop_refute vars (zip langs seps);;

let nelop langs fm = forall (nelop1 langs) (simpdnf(simplify(Not fm)));;

(* ------------------------------------------------------------------------- *)
(* Check that our example works.                                             *)
(* ------------------------------------------------------------------------- *)

(*
nelop (add_default [int_lang])
 <<f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false>>;;

(* ------------------------------------------------------------------------- *)
(* Bell numbers show the size of our case analysis.                          *)
(* ------------------------------------------------------------------------- *)

let bell n = length(allpartitions (1--n)) in map bell (1--10);;

*)

(* ------------------------------------------------------------------------- *)
(* Find the smallest subset satisfying a predicate.                          *)
(* ------------------------------------------------------------------------- *)

let rec findasubset p m l =
  if m = 0 then p [] else
  match l with
    [] -> failwith "findasubset"
  | h::t -> try findasubset (fun s -> p(h::s)) (m - 1) t
            with Failure _ -> findasubset p m t;;

let findsubset p l =
  tryfind (fun n ->
    findasubset (fun x -> if p x then x else failwith "") n l)
       (0--length l);;

(* ------------------------------------------------------------------------- *)
(* The "true" Nelson-Oppen method.                                           *)
(* ------------------------------------------------------------------------- *)

let rec nelop_refute eqs ldseps =
  try let dj = findsubset (trydps ldseps ** map negate) eqs in
      forall (fun eq ->
        nelop_refute (subtract eqs [eq])
                     (map (fun (dps,es) -> (dps,eq::es)) ldseps)) dj
  with Failure _ -> false;;

let nelop1 langs fms0 =
  let fms = homogenize langs fms0 in
  let seps = langpartition langs fms in
  let fvlist = map (unions ** map fv) seps in
  let vars = filter (fun x -> length (filter (mem x) fvlist) >= 2)
                    (unions fvlist) in
  let eqs = map (fun (a,b) -> mk_eq (Var a) (Var b))
                (distinctpairs vars) in
  nelop_refute eqs (zip langs seps);;

let nelop langs fm = forall (nelop1 langs) (simpdnf(simplify(Not fm)));;

(* ------------------------------------------------------------------------- *)
(* Some additional examples (from ICS paper and Shostak's "A practical..."   *)
(* ------------------------------------------------------------------------- *)

(*
nelop (add_default [int_lang])
 <<y <= x /\ y >= x + z /\ z >= 0 ==> f(f(x) - f(y)) = f(z)>>;;

nelop (add_default [int_lang])
 <<x = y /\ y >= z /\ z >= x ==> f(z) = f(x)>>;;

nelop (add_default [int_lang])
 <<a <= b /\ b <= f(a) /\ f(a) <= 1
  ==> a + b <= 1 \/ b + f(b) <= 1 \/ f(f(b)) <= f(a)>>;;

(* ------------------------------------------------------------------------- *)
(* Confirmation of non-convexity.                                            *)
(* ------------------------------------------------------------------------- *)

map (real_qelim ** generalize)
  [<<x * y = 0 /\ z = 0 ==> x = z \/ y = z>>;
   <<x * y = 0 /\ z = 0 ==> x = z>>;
   <<x * y = 0 /\ z = 0 ==> y = z>>];;

map (integer_qelim ** generalize)
  [<<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y \/ x = z>>;
   <<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = y>>;
   <<0 <= x /\ x < 2 /\ y = 0 /\ z = 1 ==> x = z>>];;

(* ------------------------------------------------------------------------- *)
(* Failures of original Shostak procedure.                                   *)
(* ------------------------------------------------------------------------- *)

nelop (add_default [int_lang])
 <<f(v - 1) - 1 = v + 1 /\ f(u) + 1 = u - 1 /\ u + 1 = v ==> false>>;;

(*** And this one is where the original procedure loops ***)

nelop (add_default [int_lang])
 <<f(v) = v /\ f(u) = u - 1 /\ u = v ==> false>>;;

(* ------------------------------------------------------------------------- *)
(* Additional examples not in the text.                                      *)
(* ------------------------------------------------------------------------- *)

(*** This is on p. 8 of Shostak's "Deciding combinations" paper ***)

time (nelop (add_default [int_lang]))
 <<z = f(x - y) /\ x = z + y /\ ~(-(y) = -(x - f(f(z)))) ==> false>>;;

(*** This (ICS theories-1) fails without array operations ***)

time (nelop (add_default [int_lang]))
 <<a + 2 = b ==> f(read(update(A,a,3),b-2)) = f(b - a + 1)>>;;

(*** can-001 from ICS examples site, with if-then-elses expanded manually ***)

time (nelop (add_default [int_lang]))
 <<(x = y /\ z = 1 ==> f(f((x+z))) = f(f((1+y))))>>;;

(*** RJB example; lists plus uninterpreted functions ***)

time (nelop (add_default [int_lang]))
 <<hd(x) = hd(y) /\ tl(x) = tl(y) /\ ~(x = nil) /\ ~(y = nil)
   ==> f(x) = f(y)>>;;

(*** Another one from the ICS paper ***)

time (nelop (add_default [int_lang]))
 <<~(f(f(x) - f(y)) = f(z)) /\ y <= x /\ y >= x + z /\ z >= 0 ==> false>>;;

(*** Shostak's "A Practical Decision Procedure..." paper
 *** No longer works since I didn't do predicates in congruence closure
time (nelop (add_default [int_lang]))
 <<x < f(y) + 1 /\ f(y) <= x ==> (P(x,y) <=> P(f(y),y))>>;;
 ***)

(*** Shostak's "Practical..." paper again, using extra clauses for MAX ***)

time (nelop (add_default [int_lang]))
 <<(x >= y ==> MAX(x,y) = x) /\ (y >= x ==> MAX(x,y) = y)
   ==> x = y + 2 ==> MAX(x,y) = x>>;;

(*** Shostak's "Practical..." paper again ***)

time (nelop (add_default [int_lang]))
 <<x <= g(x) /\ x >= g(x) ==> x = g(g(g(g(x))))>>;;

(*** Easy example I invented ***)

time (nelop (add_default [real_lang]))
 <<x^2 =  1 ==> (f(x) = f(-(x)))  ==> (f(x) = f(1))>>;;

(*** Taken from Clark Barrett's CVC page ***)

time (nelop (add_default [int_lang]))
 <<2 * f(x + y) = 3 * y /\ 2 * x = y ==> f(f(x + y)) = 3 * x>>;;

(*** My former running example in the text; seems too slow.
 *** Anyway this also needs extra predicates in CC

time (nelop (add_default [real_lang]))
 <<x^2 = y^2 /\ x < y /\ z^2 = z /\ x < x * z /\ P(f(1 + z))
  ==> P(f(x + y) - f(0))>>;;
 ***)

(*** An example where the "naive" procedure is slow but feasible ***)

nelop (add_default [int_lang])
 <<4 * x = 2 * x + 2 * y /\ x = f(2 * x - y) /\
  f(2 * y - x) = 3 /\ f(x) = 4 ==> false>>;;

*)
(* ========================================================================= *)
(* LCF-style basis for Tarski-style Hilbert system of first order logic.     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic first order deductive system.                                       *)
(*                                                                           *)
(* This is based on Tarski's trick for avoiding use of a substitution        *)
(* primitive. It seems about the simplest possible system we could use.      *)
(*                                                                           *)
(*  if |- p ==> q and |- p then |- q                                         *)
(*  if |- p then |- forall x. p                                              *)
(*                                                                           *)
(*  |- p ==> (q ==> p)                                                       *)
(*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
(*  |- ((p ==> false) ==> false) ==> p                                       *)
(*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
(*  |- p ==> forall x. p                            [x not free in p]        *)
(*  |- exists x. x = t                              [x not free in t]        *)
(*  |- t = t                                                                 *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
(*                                                                           *)
(*  |- (p <=> q) ==> p ==> q                                                 *)
(*  |- (p <=> q) ==> q ==> p                                                 *)
(*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
(*  |- true <=> (false ==> false)                                            *)
(*  |- ~p <=> (p ==> false)                                                  *)
(*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
(*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
(*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
(* ------------------------------------------------------------------------- *)

module type Proofsystem =
   sig type thm
       val modusponens : thm -> thm -> thm
       val gen : string -> thm -> thm
       val axiom_addimp : fol formula -> fol formula -> thm
       val axiom_distribimp :
            fol formula -> fol formula -> fol formula -> thm
       val axiom_doubleneg : fol formula -> thm
       val axiom_allimp : string -> fol formula -> fol formula -> thm
       val axiom_impall : string -> fol formula -> thm
       val axiom_existseq : string -> term -> thm
       val axiom_eqrefl : term -> thm
       val axiom_funcong : string -> term list -> term list -> thm
       val axiom_predcong : string -> term list -> term list -> thm
       val axiom_iffimp1 : fol formula -> fol formula -> thm
       val axiom_iffimp2 : fol formula -> fol formula -> thm
       val axiom_impiff : fol formula -> fol formula -> thm
       val axiom_true : thm
       val axiom_not : fol formula -> thm
       val axiom_and : fol formula -> fol formula -> thm
       val axiom_or : fol formula -> fol formula -> thm
       val axiom_exists : string -> fol formula -> thm
       val concl : thm -> fol formula
   end;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec occurs_in s t =
  s = t or
  match t with
    Var y -> false
  | Fn(f,args) -> exists (occurs_in s) args;;

let rec free_in t fm =
  match fm with
    False|True -> false
  | Atom(R(p,args)) -> exists (occurs_in t) args
  | Not(p) -> free_in t p
  | And(p,q)|Or(p,q)|Imp(p,q)|Iff(p,q) -> free_in t p or free_in t q
  | Forall(y,p)|Exists(y,p) -> not(occurs_in (Var y) t) & free_in t p;;

(* ------------------------------------------------------------------------- *)
(* Implementation of the abstract data type of theorems.                     *)
(* ------------------------------------------------------------------------- *)

module Proven : Proofsystem =
  struct
    type thm = fol formula
    let modusponens pq p =
      match pq with
        Imp(p',q) when p = p' -> q
      | _ -> failwith "modusponens"
    let gen x p = Forall(x,p)
    let axiom_addimp p q = Imp(p,Imp(q,p))
    let axiom_distribimp p q r =
      Imp(Imp(p,Imp(q,r)),Imp(Imp(p,q),Imp(p,r)))
    let axiom_doubleneg p = Imp(Imp(Imp(p,False),False),p)
    let axiom_allimp x p q =
      Imp(Forall(x,Imp(p,q)),Imp(Forall(x,p),Forall(x,q)))
    let axiom_impall x p =
      if not (free_in (Var x) p) then Imp(p,Forall(x,p))
      else failwith "axiom_impall: variable free in formula"
    let axiom_existseq x t =
      if not (occurs_in (Var x) t) then Exists(x,mk_eq (Var x) t)
      else failwith "axiom_existseq: variable free in term"
    let axiom_eqrefl t = mk_eq t t
    let axiom_funcong f lefts rights =
       itlist2 (fun s t p -> Imp(mk_eq s t,p)) lefts rights
               (mk_eq (Fn(f,lefts)) (Fn(f,rights)))
    let axiom_predcong p lefts rights =
       itlist2 (fun s t p -> Imp(mk_eq s t,p)) lefts rights
               (Imp(Atom(R(p,lefts)),Atom(R(p,rights))))
    let axiom_iffimp1 p q = Imp(Iff(p,q),Imp(p,q))
    let axiom_iffimp2 p q = Imp(Iff(p,q),Imp(q,p))
    let axiom_impiff p q = Imp(Imp(p,q),Imp(Imp(q,p),Iff(p,q)))
    let axiom_true = Iff(True,Imp(False,False))
    let axiom_not p = Iff(Not p,Imp(p,False))
    let axiom_and p q = Iff(And(p,q),Imp(Imp(p,Imp(q,False)),False))
    let axiom_or p q = Iff(Or(p,q),Not(And(Not(p),Not(q))))
    let axiom_exists x p = Iff(Exists(x,p),Not(Forall(x,Not p)))
    let concl c = c
  end;;

(* ------------------------------------------------------------------------- *)
(* A printer for theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

include Proven;;

let print_thm th =
  open_box 0;
  print_string "|-"; print_space();
  open_box 0; print_formula print_atom (concl th); close_box();
  close_box();;

#install_printer print_thm;;
(* ========================================================================= *)
(* Propositional reasoning by derived rules atop the LCF core.               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* |- p ==> p                                                                *)
(* ------------------------------------------------------------------------- *)

let imp_refl p =
  modusponens (modusponens (axiom_distribimp p (Imp(p,p)) p)
                           (axiom_addimp p (Imp(p,p))))
              (axiom_addimp p p);;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> p ==> q                                          *)
(*               -------------------- imp_unduplicate                        *)
(*                 |- p ==> q                                                *)
(* ------------------------------------------------------------------------- *)

let imp_unduplicate th =
  let p,pq = dest_imp(concl th) in
  let q = consequent pq in
  modusponens (modusponens (axiom_distribimp p p q) th) (imp_refl p);;

(* ------------------------------------------------------------------------- *)
(* Some handy syntax operations.                                             *)
(* ------------------------------------------------------------------------- *)

let negatef fm =
  match fm with
    Imp(p,False) -> p
  | p -> Imp(p,False);;

let negativef fm = match fm with Imp(p,False) -> true | _ -> false;;

(* ------------------------------------------------------------------------- *)
(*                           |- q                                            *)
(*         ------------------------------------------------ add_assum (p)    *)
(*                         |- p ==> q                                        *)
(* ------------------------------------------------------------------------- *)

let add_assum p th = modusponens (axiom_addimp (concl th) p) th;;

(* ------------------------------------------------------------------------- *)
(*                   |- q ==> r                                              *)
(*         --------------------------------------- imp_add_assum p           *)
(*           |- (p ==> q) ==> (p ==> r)                                      *)
(* ------------------------------------------------------------------------- *)

let imp_add_assum p th =
  let (q,r) = dest_imp(concl th) in
  modusponens (axiom_distribimp p q r) (add_assum p th);;

(* ------------------------------------------------------------------------- *)
(*            |- p ==> q              |- q ==> r                             *)
(*         ----------------------------------------- imp_trans               *)
(*                 |- p ==> r                                                *)
(* ------------------------------------------------------------------------- *)

let imp_trans th1 th2 =
  let p = antecedent(concl th1) in
  modusponens (imp_add_assum p th2) th1;;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> r                                                *)
(*         -------------------------- imp_insert q                           *)
(*              |- p ==> q ==> r                                             *)
(* ------------------------------------------------------------------------- *)

let imp_insert q th =
  let (p,r) = dest_imp(concl th) in
  imp_trans th (axiom_addimp r q);;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> q ==> r                                          *)
(*              ---------------------- imp_swap                              *)
(*                 |- q ==> p ==> r                                          *)
(* ------------------------------------------------------------------------- *)

let imp_swap th =
  let p,qr = dest_imp(concl th) in
  let q,r = dest_imp qr in
  imp_trans (axiom_addimp q p)
            (modusponens (axiom_distribimp p q r) th);;

(* ------------------------------------------------------------------------- *)
(* |- (q ==> r) ==> (p ==> q) ==> (p ==> r)                                  *)
(* ------------------------------------------------------------------------- *)

let imp_trans_th p q r =
   imp_trans (axiom_addimp (Imp(q,r)) p)
             (axiom_distribimp p q r);;

(* ------------------------------------------------------------------------- *)
(*                 |- p ==> q                                                *)
(*         ------------------------------- imp_add_concl r                   *)
(*          |- (q ==> r) ==> (p ==> r)                                       *)
(* ------------------------------------------------------------------------- *)

let imp_add_concl r th =
  let (p,q) = dest_imp(concl th) in
  modusponens (imp_swap(imp_trans_th p q r)) th;;

(* ------------------------------------------------------------------------- *)
(* |- (p ==> q ==> r) ==> (q ==> p ==> r)                                    *)
(* ------------------------------------------------------------------------- *)

let imp_swap_th p q r =
  imp_trans (axiom_distribimp p q r)
            (imp_add_concl (Imp(p,r)) (axiom_addimp q p));;

(* ------------------------------------------------------------------------- *)
(*  |- (p ==> q ==> r) ==> (s ==> t ==> u)                                   *)
(* -----------------------------------------                                 *)
(*  |- (q ==> p ==> r) ==> (t ==> s ==> u)                                   *)
(* ------------------------------------------------------------------------- *)

let imp_swap2 th =
  match concl th with
    Imp(Imp(p,Imp(q,r)),Imp(s,Imp(t,u))) ->
        imp_trans (imp_swap_th q p r) (imp_trans th (imp_swap_th s t u))
  | _ -> failwith "imp_swap2";;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r and |- p ==> q then |- p ==> r.                       *)
(* ------------------------------------------------------------------------- *)

let right_mp ith th =
  imp_unduplicate(imp_trans th (imp_swap ith));;

(* ------------------------------------------------------------------------- *)
(*                 |- p <=> q                                                *)
(*                ------------ iff_imp1                                      *)
(*                 |- p ==> q                                                *)
(* ------------------------------------------------------------------------- *)

let iff_imp1 th =
  let (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp1 p q) th;;

(* ------------------------------------------------------------------------- *)
(*                 |- p <=> q                                                *)
(*                ------------ iff_imp2                                      *)
(*                 |- q ==> p                                                *)
(* ------------------------------------------------------------------------- *)

let iff_imp2 th =
  let (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp2 p q) th;;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q      |- q ==> p                                        *)
(*        ---------------------------- imp_antisym                           *)
(*              |- p <=> q                                                   *)
(* ------------------------------------------------------------------------- *)

let imp_antisym th1 th2 =
  let (p,q) = dest_imp(concl th1) in
  modusponens (modusponens (axiom_impiff p q) th1) th2;;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> (q ==> false) ==> false                                  *)
(*       ----------------------------------- right_doubleneg                 *)
(*               |- p ==> q                                                  *)
(* ------------------------------------------------------------------------- *)

let right_doubleneg th =
  match concl th with
    Imp(_,Imp(Imp(p,False),False)) -> imp_trans th (axiom_doubleneg p)
  | _ -> failwith "right_doubleneg";;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*         ------------------------------------------- ex_falso (p)          *)
(*                 |- false ==> p                                            *)
(* ------------------------------------------------------------------------- *)

let ex_falso p = right_doubleneg(axiom_addimp False (Imp(p,False)));;

(* ------------------------------------------------------------------------- *)
(*  |- p ==> q ==> r        |- r ==> s                                       *)
(* ------------------------------------ imp_trans2                           *)
(*      |- p ==> q ==> s                                                     *)
(* ------------------------------------------------------------------------- *)

let imp_trans2 th1 th2 =
  let Imp(p,Imp(q,r)) = concl th1 and Imp(r',s) = concl th2 in
  let th = imp_add_assum p (modusponens (imp_trans_th q r s) th2) in
  modusponens th th1;;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q1   ...   |- p ==> qn   |- q1 ==> ... ==> qn ==> r      *)
(*        --------------------------------------------------------------     *)
(*                             |- p ==> r                                    *)
(* ------------------------------------------------------------------------- *)

let imp_trans_chain
 ths th =
  itlist (fun a b -> imp_unduplicate (imp_trans a (imp_swap b)))
         (rev(tl ths)) (imp_trans (hd ths) th);;

(* ------------------------------------------------------------------------- *)
(* |- (q ==> false) ==> p ==> (p ==> q) ==> false                            *)
(* ------------------------------------------------------------------------- *)

let imp_truefalse p q =
  imp_trans (imp_trans_th p q False) (imp_swap_th (Imp(p,q)) p False);;

(* ------------------------------------------------------------------------- *)
(*  |- (p' ==> p) ==> (q ==> q') ==> (p ==> q) ==> (p' ==> q')               *)
(* ------------------------------------------------------------------------- *)

let imp_mono_th p p' q q' =
  let th1 = imp_trans_th (Imp(p,q)) (Imp(p',q)) (Imp(p',q'))
  and th2 = imp_trans_th p' q q'
  and th3 = imp_swap(imp_trans_th p' p q) in
  imp_trans th3 (imp_swap(imp_trans th2 th1));;

(* ------------------------------------------------------------------------- *)
(* |- true                                                                   *)
(* ------------------------------------------------------------------------- *)

let truth = modusponens (iff_imp2 axiom_true) (imp_refl False);;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> q                                                        *)
(*      ----------------- contrapos                                          *)
(*         |- ~q ==> ~p                                                      *)
(* ------------------------------------------------------------------------- *)

let contrapos th =
  let p,q = dest_imp(concl th) in
  imp_trans (imp_trans (iff_imp1(axiom_not q)) (imp_add_concl False th))
            (iff_imp2(axiom_not p));;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> p                                                           *)
(* ------------------------------------------------------------------------- *)

let and_left p q =
  let th1 = imp_add_assum p (axiom_addimp False q) in
  let th2 = right_doubleneg(imp_add_concl False th1) in
  imp_trans (iff_imp1(axiom_and p q)) th2;;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> q                                                           *)
(* ------------------------------------------------------------------------- *)

let and_right p q =
  let th1 = axiom_addimp (Imp(q,False)) p in
  let th2 = right_doubleneg(imp_add_concl False th1) in
  imp_trans (iff_imp1(axiom_and p q)) th2;;

(* ------------------------------------------------------------------------- *)
(* |- p1 /\ ... /\ pn ==> pi for each 1 <= i <= n (input term right assoc)   *)
(* ------------------------------------------------------------------------- *)

let rec conjths fm =
  try let p,q = dest_and fm in
      (and_left p q)::map (imp_trans (and_right p q)) (conjths q)
  with Failure _ -> [imp_refl fm];;

(* ------------------------------------------------------------------------- *)
(* |- p ==> q ==> p /\ q                                                     *)
(* ------------------------------------------------------------------------- *)

let and_pair p q =
  let th1 = iff_imp2(axiom_and p q)
  and th2 = imp_swap_th (Imp(p,Imp(q,False))) q False in
  let th3 = imp_add_assum p (imp_trans2 th2 th1) in
  modusponens th3 (imp_swap (imp_refl (Imp(p,Imp(q,False)))));;

(* ------------------------------------------------------------------------- *)
(* If |- p /\ q ==> r then |- p ==> q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

let shunt th =
  let p,q = dest_and(antecedent(concl th)) in
  modusponens (itlist imp_add_assum [p;q] th) (and_pair p q);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r then |- p /\ q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

let unshunt th =
  let p,qr = dest_imp(concl th) in
  let q,r = dest_imp qr in
  imp_trans_chain [and_left p q; and_right p q] th;;

(* ------------------------------------------------------------------------- *)
(* Produce |- (p <=> q) <=> (p ==> q) /\ (q ==> p)                           *)
(* ------------------------------------------------------------------------- *)

let iff_def p q =
  let th1 = and_pair (Imp(p,q)) (Imp(q,p)) in
  let th2 = imp_trans_chain [axiom_iffimp1 p q; axiom_iffimp2 p q] th1 in
  imp_antisym th2 (unshunt (axiom_impiff p q));;

let iff_def p q =
  let th = and_pair (Imp(p,q)) (Imp(q,p))
  and thl = [axiom_iffimp1 p q; axiom_iffimp2 p q] in
  imp_antisym (imp_trans_chain thl th) (unshunt (axiom_impiff p q));;

(* ------------------------------------------------------------------------- *)
(* Produce "expansion" theorem for defined connectives.                      *)
(* ------------------------------------------------------------------------- *)

let expand_connective fm =
  match fm with
    True -> axiom_true
  | Not p -> axiom_not p
  | And(p,q) -> axiom_and p q
  | Or(p,q) -> axiom_or p q
  | Iff(p,q) -> iff_def p q
  | Exists(x,p) -> axiom_exists x p
  | _ -> failwith "expand_connective";;

let eliminate_connective fm =
  if not(negativef fm) then iff_imp1(expand_connective fm)
  else imp_add_concl False (iff_imp2(expand_connective(negatef fm)));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   ------------------------------------------------- imp_false_conseqs     *)
(*      [|- ((p ==> q) ==> false) ==> (q ==> false);                         *)
(*       |- ((p ==> q) ==> false) ==> p]                                     *)
(* ------------------------------------------------------------------------- *)

let imp_false_conseqs p q =
 [right_doubleneg(imp_add_concl False (imp_add_assum p (ex_falso q)));
  imp_add_concl False (imp_insert p (imp_refl q))];;

(* ------------------------------------------------------------------------- *)
(*         |- p ==> (q ==> false) ==> r                                      *)
(*        ------------------------------------ imp_false_rule                *)
(*             |- ((p ==> q) ==> false) ==> r                                *)
(* ------------------------------------------------------------------------- *)

let imp_false_rule th =
  let p,r = dest_imp (concl th) in
  imp_trans_chain (imp_false_conseqs p (funpow 2 antecedent r)) th;;

(* ------------------------------------------------------------------------- *)
(*         |- (p ==> false) ==> r          |- q ==> r                        *)
(*       ---------------------------------------------- imp_true_rule        *)
(*                      |- (p ==> q) ==> r                                   *)
(* ------------------------------------------------------------------------- *)

let imp_true_rule th1 th2 =
  let p = funpow 2 antecedent (concl th1) and q = antecedent(concl th2)
  and th3 = right_doubleneg(imp_add_concl False th1)
  and th4 = imp_add_concl False th2 in
  let th5 = imp_swap(imp_truefalse p q) in
  let th6 = imp_add_concl False (imp_trans_chain [th3; th4] th5)
  and th7 = imp_swap(imp_refl(Imp(Imp(p,q),False))) in
  right_doubleneg(imp_trans th7 th6);;

(* ------------------------------------------------------------------------- *)
(*                                 *                                         *)
(*                 -------------------------------------- imp_contr          *)
(*                        |- p ==> -p ==> q                                  *)
(* ------------------------------------------------------------------------- *)

let imp_contr p q =
  if negativef p then imp_add_assum (negatef p) (ex_falso q)
  else imp_swap (imp_add_assum p (ex_falso q));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------------------- imp_front (this antecedent) *)
(*  |- (p0 ==> p1 ==> ... ==> pn ==> q)                                      *)
(*     ==> pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                              *)
(* ------------------------------------------------------------------------- *)

let rec imp_front_th n fm =
  if n = 0 then imp_refl fm else
  let p,qr = dest_imp fm in
  let th1 = imp_add_assum p (imp_front_th (n - 1) qr) in
  let q',r' = dest_imp(funpow 2 consequent(concl th1)) in
  imp_trans th1 (imp_swap_th p q' r');;

(* ------------------------------------------------------------------------- *)
(*           |- p0 ==> p1 ==> ... ==> pn ==> q                               *)
(*         ------------------------------------------ imp_front n            *)
(*           |- pn ==> p0 ==> p1 ==> .. p(n-1) ==> q                         *)
(* ------------------------------------------------------------------------- *)

let imp_front n th = modusponens (imp_front_th n (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Propositional tableaux procedure.                                         *)
(* ------------------------------------------------------------------------- *)

let rec lcfptab fms lits =
  match fms with
    False::fl ->
        ex_falso (itlist mk_imp (fl @ lits) False)
  | (Imp(p,q) as fm)::fl when p = q ->
        add_assum fm (lcfptab fl lits)
  | Imp(Imp(p,q),False)::fl ->
        imp_false_rule(lcfptab (p::Imp(q,False)::fl) lits)
  | Imp(p,q)::fl when q <> False ->
        imp_true_rule (lcfptab (Imp(p,False)::fl) lits)
                      (lcfptab (q::fl) lits)
  | (Atom(_)|Forall(_,_)|Imp((Atom(_)|Forall(_,_)),False) as p)::fl ->
        if mem (negatef p) lits then
          let l1,l2 = chop_list (index (negatef p) lits) lits in
          let th = imp_contr p (itlist mk_imp (tl l2) False) in
          itlist imp_insert (fl @ l1) th
        else imp_front (length fl) (lcfptab fl (p::lits))
  | fm::fl ->
        let th = eliminate_connective fm in
        imp_trans th (lcfptab (consequent(concl th)::fl) lits)
  | _ -> failwith "lcfptab: no contradiction";;

(* ------------------------------------------------------------------------- *)
(* In particular, this gives a tautology prover.                             *)
(* ------------------------------------------------------------------------- *)

let lcftaut p =
  modusponens (axiom_doubleneg p) (lcfptab [negatef p] []);;

(* ------------------------------------------------------------------------- *)
(* The examples in the text.                                                 *)
(* ------------------------------------------------------------------------- *)

(*
lcftaut <<(p ==> q) \/ (q ==> p)>>;;

lcftaut <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

lcftaut <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;
*)
(* ========================================================================= *)
(* First-order derived rules in the LCF setup.                               *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*                         ******                                            *)
(*         ------------------------------------------ eq_sym                 *)
(*                      |- s = t ==> t = s                                   *)
(* ------------------------------------------------------------------------- *)

let eq_sym s t =
  let rth = axiom_eqrefl s in
  funpow 2 (fun th -> modusponens (imp_swap th) rth)
           (axiom_predcong "=" [s; s] [t; s]);;

(* ------------------------------------------------------------------------- *)
(* |- s = t ==> t = u ==> s = u.                                             *)
(* ------------------------------------------------------------------------- *)

let eq_trans s t u =
  let th1 = axiom_predcong "=" [t; u] [s; u] in
  let th2 = modusponens (imp_swap th1) (axiom_eqrefl u) in
  imp_trans (eq_sym s t) th2;;

(* ------------------------------------------------------------------------- *)
(*         ---------------------------- icongruence                          *)
(*          |- s = t ==> tm[s] = tm[t]                                       *)
(* ------------------------------------------------------------------------- *)

let rec icongruence s t stm ttm =
  if stm = ttm then add_assum (mk_eq s t) (axiom_eqrefl stm)
  else if stm = s & ttm = t then imp_refl (mk_eq s t) else
  match (stm,ttm) with
   (Fn(fs,sa),Fn(ft,ta)) when fs = ft & length sa = length ta ->
        let ths = map2 (icongruence s t) sa ta in
        let ts = map (consequent ** concl) ths in
        imp_trans_chain ths (axiom_funcong fs (map lhs ts) (map rhs ts))
  | _ -> failwith "icongruence: not congruent";;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
icongruence <<|s|>> <<|t|>> <<|f(s,g(s,t,s),u,h(h(s)))|>>
                            <<|f(s,g(t,t,s),u,h(h(t)))|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* |- (forall x. p ==> q(x)) ==> p ==> (forall x. q(x))                      *)
(* ------------------------------------------------------------------------- *)

let gen_right_th x p q =
  imp_swap(imp_trans (axiom_impall x p) (imp_swap(axiom_allimp x p q)));;

(* ------------------------------------------------------------------------- *)
(*                       |- p ==> q                                          *)
(*         ------------------------------------- genimp "x"                  *)
(*           |- (forall x. p) ==> (forall x. q)                              *)
(* ------------------------------------------------------------------------- *)

let genimp x th =
  let p,q = dest_imp(concl th) in
  modusponens (axiom_allimp x p q) (gen x th);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q[x] then |- p ==> forall x. q[x]                             *)
(* ------------------------------------------------------------------------- *)

let gen_right x th =
  let p,q = dest_imp(concl th) in
  modusponens (gen_right_th x p q) (gen x th);;

(* ------------------------------------------------------------------------- *)
(* |- (forall x. p(x) ==> q) ==> (exists x. p(x)) ==> q                      *)
(* ------------------------------------------------------------------------- *)

let exists_left_th x p q =
  let p' = Imp(p,False) and q' = Imp(q,False) in
  let th1 = genimp x (imp_swap(imp_trans_th p q False)) in
  let th2 = imp_trans th1 (gen_right_th x q' p') in
  let th3 = imp_swap(imp_trans_th q' (Forall(x,p')) False) in
  let th4 = imp_trans2 (imp_trans th2 th3) (axiom_doubleneg q) in
  let th5 = imp_add_concl False (genimp x (iff_imp2 (axiom_not p))) in
  let th6 = imp_trans (iff_imp1 (axiom_not (Forall(x,Not p)))) th5 in
  let th7 = imp_trans (iff_imp1(axiom_exists x p)) th6 in
  imp_swap(imp_trans th7 (imp_swap th4));;

(* ------------------------------------------------------------------------- *)
(* If |- p(x) ==> q then |- (exists x. p(x)) ==> q                           *)
(* ------------------------------------------------------------------------- *)

let exists_left x th =
  let p,q = dest_imp(concl th) in
  modusponens (exists_left_th x p q) (gen x th);;

(* ------------------------------------------------------------------------- *)
(*    |- x = t ==> p ==> q    [x not in t and not free in q]                 *)
(*  --------------------------------------------------------------- subspec  *)
(*                 |- (forall x. p) ==> q                                    *)
(* ------------------------------------------------------------------------- *)

let subspec th =
  match concl th with
    Imp(Atom(R("=",[Var x;t])) as e,Imp(p,q)) ->
        let th1 = imp_trans (genimp x (imp_swap th))
                            (exists_left_th x e q) in
        modusponens (imp_swap th1) (axiom_existseq x t)
  | _ -> failwith "subspec: wrong sort of theorem";;

(* ------------------------------------------------------------------------- *)
(*    |- x = y ==> p[x] ==> q[y]  [x not in FV(q); y not in FV(p) or x == y] *)
(*  --------------------------------------------------------- subalpha       *)
(*                 |- (forall x. p) ==> (forall y. q)                        *)
(* ------------------------------------------------------------------------- *)

let subalpha th =
   match concl th with
    Imp(Atom(R("=",[Var x;Var y])),Imp(p,q)) ->
        if x = y then genimp x (modusponens th (axiom_eqrefl(Var x)))
        else gen_right y (subspec th)
  | _ -> failwith "subalpha: wrong sort of theorem";;

(* ------------------------------------------------------------------------- *)
(*         ---------------------------------- isubst                         *)
(*            |- s = t ==> p[s] ==> p[t]                                     *)
(* ------------------------------------------------------------------------- *)

let rec isubst s t sfm tfm =
  if sfm = tfm then add_assum (mk_eq s t) (imp_refl tfm) else
  match (sfm,tfm) with
    Atom(R(p,sa)),Atom(R(p',ta)) when p = p' & length sa = length ta ->
        let ths = map2 (icongruence s t) sa ta in
        let ls,rs = unzip (map (dest_eq ** consequent ** concl) ths) in
        imp_trans_chain ths (axiom_predcong p ls rs)
  | Imp(sp,sq),Imp(tp,tq) ->
        let th1 = imp_trans (eq_sym s t) (isubst t s tp sp)
        and th2 = isubst s t sq tq in
        imp_trans_chain [th1; th2] (imp_mono_th sp tp sq tq)
  | Forall(x,p),Forall(y,q) ->
        if x = y then
          imp_trans (gen_right x (isubst s t p q)) (axiom_allimp x p q)
        else
          let z = Var(variant x (unions [fv p; fv q; fvt s; fvt t])) in
          let th1 = isubst (Var x) z p (subst (x |=> z) p)
          and th2 = isubst z (Var y) (subst (y |=> z) q) q in
          let th3 = subalpha th1 and th4 = subalpha th2 in
          let th5 = isubst s t (consequent(concl th3))
                               (antecedent(concl th4)) in
          imp_swap (imp_trans2 (imp_trans th3 (imp_swap th5)) th4)
  | _ ->
        let sth = iff_imp1(expand_connective sfm)
        and tth = iff_imp2(expand_connective tfm) in
        let th1 = isubst s t (consequent(concl sth))
                             (antecedent(concl tth)) in
        imp_swap(imp_trans sth (imp_swap(imp_trans2 th1 tth)));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* -------------------------------------------- alpha "z" <<forall x. p[x]>> *)
(*   |- (forall x. p[x]) ==> (forall z. p'[z])                               *)
(*                                                                           *)
(* [Restriction that z is not free in the initial p[x].]                     *)
(* ------------------------------------------------------------------------- *)

let alpha z fm =
  match fm with
    Forall(x,p) -> let p' = subst (x |=> Var z) p in
                   subalpha(isubst (Var x) (Var z) p p')
  | _ -> failwith "alpha: not a universal formula";;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* -------------------------------- ispec t <<forall x. p[x]>>               *)
(*   |- (forall x. p[x]) ==> p'[t]                                           *)
(* ------------------------------------------------------------------------- *)

let rec ispec t fm =
  match fm with
    Forall(x,p) ->
      if mem x (fvt t) then
        let th = alpha (variant x (union (fvt t) (var p))) fm in
        imp_trans th (ispec t (consequent(concl th)))
      else subspec(isubst (Var x) t p (subst (x |=> t) p))
  | _ -> failwith "ispec: non-universal formula";;

(* ------------------------------------------------------------------------- *)
(* Specialization rule.                                                      *)
(* ------------------------------------------------------------------------- *)

let spec t th = modusponens (ispec t (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

(*
ispec <<|y|>> <<forall x y z. x + y + z = z + y + x>>;;

(* ------------------------------------------------------------------------- *)
(* Additional tests not in main text.                                        *)
(* ------------------------------------------------------------------------- *)

isubst <<|x + x|>> <<|2 * x|>>
        <<x + x = x ==> x = 0>> <<2 * x = x ==> x = 0>>;;

isubst <<|x + x|>>  <<|2 * x|>>
       <<(x + x = y + y) ==> (y + y + y = x + x + x)>>
       <<2 * x = y + y ==> y + y + y = x + 2 * x>>;;

ispec <<|x|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x|>> <<forall x. x = x>> ;;

ispec <<|w + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x + y + z|>> <<forall x y z. nothing_much>> ;;

isubst <<|x + x|>> <<|2 * x|>>
       <<(x + x = y + y) <=> (something \/ y + y + y = x + x + x)>> ;;

isubst <<|x + x|>>  <<|2 * x|>>
       <<(exists x. x = 2) <=> exists y. y + x + x = y + y + y>>
       <<(exists x. x = 2) <=> (exists y. y + 2 * x = y + y + y)>>;;

isubst <<|x|>>  <<|y|>>
        <<(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)>>
        <<(forall z. y = z) <=> (exists x. y < z) /\ (forall y'. y' < y)>>;;

(* ------------------------------------------------------------------------- *)
(* The bug is now fixed.                                                     *)
(* ------------------------------------------------------------------------- *)

ispec <<|x'|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec <<|x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec <<|x' + x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec <<|x + x' + x''|>> <<forall x x' x''. x + x' + x'' = 0>>;;

ispec <<|2 * x|>> <<forall x x'. x + x' = x' + x>>;;

*)
(* ========================================================================= *)
(* First order tableau procedure using LCF setup.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unification of complementary literals.                                    *)
(* ------------------------------------------------------------------------- *)

let unify_complementsf env =
  function (Atom(R(p1,a1)),Imp(Atom(R(p2,a2)),False))
         | (Imp(Atom(R(p1,a1)),False),Atom(R(p2,a2)))
               -> unify env [Fn(p1,a1),Fn(p2,a2)]
         | _ -> failwith "unify_complementsf";;

(* ------------------------------------------------------------------------- *)
(*    |- (q ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* --------------------------------------------- use_laterimp <<q ==> p>>    *)
(*    |- (p ==> f) ==> ... ==> (q ==> p) ==> r                               *)
(* ------------------------------------------------------------------------- *)

let rec use_laterimp i fm =
  match fm with
    Imp(Imp(q',s),Imp(Imp(q,p) as i',r)) when i' = i ->
        let th1 = axiom_distribimp i (Imp(Imp(q,s),r)) (Imp(Imp(p,s),r))
        and th2 = imp_swap(imp_trans_th q p s)
        and th3 = imp_swap(imp_trans_th (Imp(p,s)) (Imp(q,s)) r) in
        imp_swap2(modusponens th1 (imp_trans th2 th3))
  | Imp(qs,Imp(a,b)) ->
        imp_swap2(imp_add_assum a (use_laterimp i (Imp(qs,b))));;

(* ------------------------------------------------------------------------- *)
(* The "closure" inference rules.                                            *)
(* ------------------------------------------------------------------------- *)

let imp_false_rule' th es = imp_false_rule(th es);;

let imp_true_rule' th1 th2 es = imp_true_rule (th1 es) (th2 es);;

let imp_front' n thp es = imp_front n (thp es);;

let add_assum' fm thp (e,s as es) =
  add_assum (onformula e fm) (thp es);;

let eliminate_connective' fm thp (e,s as es) =
  imp_trans (eliminate_connective (onformula e fm)) (thp es);;

let spec' y fm n thp (e,s) =
  let th = imp_swap(imp_front n (thp(e,s))) in
  imp_unduplicate(imp_trans (ispec (e y) (onformula e fm)) th);;

let ex_falso' fms (e,s) =
  ex_falso (itlist (mk_imp ** onformula e) fms s);;

let complits' (p::fl,lits) i (e,s) =
  let l1,p'::l2 = chop_list i lits in
  itlist (imp_insert ** onformula e) (fl @ l1)
         (imp_contr (onformula e p)
                    (itlist (mk_imp ** onformula e) l2 s));;

let deskol' (skh:fol formula) thp (e,s) =
  let th = thp (e,s) in
  modusponens (use_laterimp (onformula e skh) (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Main refutation function.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec lcftab skofun (fms,lits,n) cont (env,sks,k as esk) =
  if n < 0 then failwith "lcftab: no proof" else
  match fms with
    False::fl -> cont (ex_falso' (fl @ lits)) esk
  | (Imp(p,q) as fm)::fl when p = q ->
      lcftab skofun (fl,lits,n) (cont ** add_assum' fm) esk
  | Imp(Imp(p,q),False)::fl ->
      lcftab skofun (p::Imp(q,False)::fl,lits,n)
                    (cont ** imp_false_rule') esk
  | Imp(p,q)::fl when q <> False ->
      lcftab skofun (Imp(p,False)::fl,lits,n)
        (fun th -> lcftab skofun (q::fl,lits,n)
                                 (cont ** imp_true_rule' th)) esk
  | ((Atom(_)|Imp(Atom(_),False)) as p)::fl ->
      (try tryfind (fun p' ->
          let env' = unify_complementsf env (p,p') in
          cont(complits' (fms,lits) (index p' lits)) (env',sks,k)) lits
       with Failure _ ->
          lcftab skofun (fl,p::lits,n)
                        (cont ** imp_front' (length fl)) esk)
  | (Forall(x,p) as fm)::fl ->
      let y = Var("X_"^string_of_int k) in
      lcftab skofun ((subst (x |=> y) p)::fl@[fm],lits,n-1)
                    (cont ** spec' y fm (length fms)) (env,sks,k+1)
  | (Imp(Forall(y,p) as yp,False))::fl ->
      let fx = skofun yp in
      let p' = subst(y |=> fx) p in
      let skh = Imp(p',Forall(y,p)) in
      let sks' = (Forall(y,p),fx)::sks in
      lcftab skofun (Imp(p',False)::fl,lits,n)
                    (cont ** deskol' skh) (env,sks',k)
  | fm::fl ->
      let fm' = consequent(concl(eliminate_connective fm)) in
      lcftab skofun (fm'::fl,lits,n)
                    (cont ** eliminate_connective' fm) esk
  | [] -> failwith "lcftab: No contradiction";;

(* ------------------------------------------------------------------------- *)
(* Identify quantified subformulas; true = exists, false = forall. This is   *)
(* taking into account the effective parity.                                 *)
(* NB: maybe I can use this in sigma/delta/pi determination.                 *)
(* ------------------------------------------------------------------------- *)

let rec quantforms e fm =
  match fm with
    Not(p) -> quantforms (not e) p
  | And(p,q) | Or(p,q) -> union (quantforms e p) (quantforms e q)
  | Imp(p,q) -> quantforms e (Or(Not p,q))
  | Iff(p,q) -> quantforms e (Or(And(p,q),And(Not p,Not q)))
  | Exists(x,p) -> if e then fm::(quantforms e p) else quantforms e p
  | Forall(x,p) -> if e then quantforms e p else fm::(quantforms e p)
  | _ -> [];;

(* ------------------------------------------------------------------------- *)
(* Now create some Skolem functions.                                         *)
(* ------------------------------------------------------------------------- *)

let skolemfuns fm =
  let fns = map fst (functions fm)
  and skts = map (function Exists(x,p) -> Forall(x,Not p) | p -> p)
                 (quantforms true fm) in
  let skofun i (Forall(y,p) as ap) =
    let vars = map (fun v -> Var v) (fv ap) in
    ap,Fn(variant("f"^"_"^string_of_int i) fns,vars) in
  map2 skofun (1--length skts) skts;;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec form_match (f1,f2 as fp) env =
  match fp with
    False,False | True,True -> env
  | Atom(R(p,pa)),Atom(R(q,qa)) -> term_match env [Fn(p,pa),Fn(q,qa)]
  | Not(p1),Not(p2) -> form_match (p1,p2) env
  | And(p1,q1),And(p2,q2)| Or(p1,q1),Or(p2,q2) | Imp(p1,q1),Imp(p2,q2)
  | Iff(p1,q1),Iff(p2,q2) -> form_match (p1,p2) (form_match (q1,q2) env)
  | (Forall(x1,p1),Forall(x2,p2) |
     Exists(x1,p1),Exists(x2,p2)) when x1 = x2 ->
        let z = variant x1 (union (fv p1) (fv p2)) in
        let inst_fn = subst (x1 |=> Var z) in
        undefine z (form_match (inst_fn p1,inst_fn p2) env)
  | _ -> failwith "form_match";;

(* ------------------------------------------------------------------------- *)
(* With the current approach to picking Skolem functions.                    *)
(* ------------------------------------------------------------------------- *)

let lcfrefute fm n cont =
  let sl = skolemfuns fm in
  let find_skolem fm =
    tryfind(fun (f,t) -> tsubst(form_match (f,fm) undefined) t) sl in
  lcftab find_skolem ([fm],[],n) cont (undefined,[],0);;

(* ------------------------------------------------------------------------- *)
(* A quick demo before doing deskolemization.                                *)
(* ------------------------------------------------------------------------- *)

let mk_skol (Forall(y,p),fx) q =
  Imp(Imp(subst (y |=> fx) p,Forall(y,p)),q);;

let simpcont thp (env,sks,k) =
  let ifn = tsubst(solve env) in
  thp(ifn,onformula ifn (itlist mk_skol sks False));;

lcfrefute <<p(1) /\ ~q(1) /\ (forall x. p(x) ==> q(x))>> 1 simpcont;;

lcfrefute <<(exists x. ~p(x)) /\ (forall x. p(x))>> 1 simpcont;;

(* ------------------------------------------------------------------------- *)
(*         |- (p(v) ==> forall x. p(x)) ==> q                                *)
(*       -------------------------------------- elim_skolemvar               *)
(*                   |- q                                                    *)
(* ------------------------------------------------------------------------- *)

let elim_skolemvar th =
  match concl th with
    Imp(Imp(pv,(Forall(x,px) as apx)),q) ->
        let [th1;th2] = map (imp_trans(imp_add_concl False th))
                            (imp_false_conseqs pv apx) in
        let v = hd(subtract (fv pv) (fv apx) @ [x]) in
        let th3 = gen_right v th1 in
        let th4 = imp_trans th3 (alpha x (consequent(concl th3))) in
        modusponens (axiom_doubleneg q) (right_mp th2 th4)
  | _ -> failwith "elim_skolemvar";;

(* ------------------------------------------------------------------------- *)
(* Top continuation with careful sorting and variable replacement.           *)
(* Also need to delete post-instantiation duplicates! This shows up more     *)
(* often now that we have adequate sharing.                                  *)
(* ------------------------------------------------------------------------- *)

let deskolcont thp (env,sks,k) =
  let ifn = tsubst(solve env) in
  let isk = setify(map (fun (p,t) -> onformula ifn p,ifn t) sks) in
  let ssk = sort (decreasing (termsize ** snd)) isk in
  let vs = map (fun i -> Var("Y_"^string_of_int i)) (1--length ssk) in
  let vfn =
    replacet(itlist2 (fun (p,t) v -> t |-> v) ssk vs undefined) in
  let th = thp(vfn ** ifn,onformula vfn (itlist mk_skol ssk False)) in
  repeat (elim_skolemvar ** imp_swap) th;;

(* ------------------------------------------------------------------------- *)
(* Overall first-order prover.                                               *)
(* ------------------------------------------------------------------------- *)

let lcffol fm =
  let fvs = fv fm in
  let fm' = Imp(itlist mk_forall fvs fm,False) in
  let th1 = deepen (fun n -> lcfrefute fm' n deskolcont) 0 in
  let th2 = modusponens (axiom_doubleneg (negatef fm')) th1 in
  itlist (fun v -> spec(Var v)) (rev fvs) th2;;

(* ------------------------------------------------------------------------- *)
(* Examples in the text.                                                     *)
(* ------------------------------------------------------------------------- *)

(*
let p58 = lcffol
 <<forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let ewd1062_1 = lcffol
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* More exhaustive set of tests not in the main text.                        *)
(* ------------------------------------------------------------------------- *)

(*

let start_time = Sys.time();;

let p1 = time lcftaut
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time lcftaut
 <<~ ~p <=> p>>;;

let p3 = time lcftaut
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time lcftaut
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time lcftaut
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time lcftaut
 <<p \/ ~p>>;;

let p7 = time lcftaut
 <<p \/ ~ ~ ~p>>;;

let p8 = time lcftaut
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time lcftaut
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time lcftaut
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time lcftaut
 <<p <=> p>>;;

let p12 = time lcftaut
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time lcftaut
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time lcftaut
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time lcftaut
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time lcftaut
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time lcftaut
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p1 = time lcffol
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time lcffol
 <<~ ~p <=> p>>;;

let p3 = time lcffol
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time lcffol
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time lcffol
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time lcffol
 <<p \/ ~p>>;;

let p7 = time lcffol
 <<p \/ ~ ~ ~p>>;;

let p8 = time lcffol
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time lcffol
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time lcffol
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time lcffol
 <<p <=> p>>;;

let p12 = time lcffol
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time lcffol
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time lcffol
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time lcffol
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time lcffol
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time lcffol
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p18 = time lcffol
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time lcffol
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time lcffol
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = time lcffol
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time lcffol
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time lcffol
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time lcffol
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time lcffol
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x)))
   ==> (exists x. Q(x) /\ P(x))>>;;

let p26 = time lcffol
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y)))
   ==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time lcffol
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x))
   ==> (forall x. V(x) ==> ~R(x))
       ==> (forall x. U(x) ==> ~V(x))>>;;

let p28 = time lcffol
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time lcffol
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time lcffol
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x))
   ==> (forall x. U(x))>>;;

let p31 = time lcffol
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\
   (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x))
   ==> (exists x. Q(x) /\ J(x))>>;;

let p32 = time lcffol
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time lcffol
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

(***** NEWLY HARD

let p34 = time lcffol
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

 *****)

let p35 = time lcffol
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

let p36 = time lcffol
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time lcffol
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time lcffol
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time lcffol
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time lcffol
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time lcffol
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time lcffol
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

(***** SEEMS HARD
let p43 = time lcffol
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;
 *****)

let p44 = time lcffol
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

(**** SEEMS HARD

let p45 = time lcffol
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
 ******)

let p55 = time lcffol
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

let p57 = time lcffol
 <<P(f(a,b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall x y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

let p58 = time lcffol
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time lcffol
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time lcffol
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

let gilmore_3 = time lcffol
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time lcffol
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time lcffol
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time lcffol
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time lcffol
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time lcffol
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_9 = time lcffol
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
         ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
             (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

let davis_putnam_example = time lcffol
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

let ewd1062_1 = time lcffol
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;

let ewd1062_2 = time lcffol
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> g(x) <= g(y))>>;;

let finish_time = Sys.time() in
print_string
 ("Complete CPU time (user): "^
  (string_of_float(finish_time -. start_time)));;
  print_newline();;

*)
(* ========================================================================= *)
(* Goals, LCF-like tactics and Mizar-like proofs.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type goals =
  Goals of ((string * fol formula) list * fol formula)list *
           (thm list -> thm);;

(* ------------------------------------------------------------------------- *)
(* Printer for goals (just shows first goal plus total number).              *)
(* ------------------------------------------------------------------------- *)

let print_goal =
  let print_hyp (l,fm) =
    open_hbox(); print_string(l^":"); print_space();
    print_formula print_atom fm; print_newline(); close_box() in
  fun (Goals(gls,jfn)) ->
    match gls with
      (asl,w)::ogls ->
         print_newline();
         (if ogls = [] then print_string "1 subgoal:" else
          (print_int (length gls);
           print_string " subgoals starting with"));
         print_newline();
         do_list print_hyp (rev asl);
         print_string "---> ";
         open_hvbox 0; print_formula print_atom w; close_box();
         print_newline()
    | [] -> print_string "No subgoals";;

#install_printer print_goal;;

(* ------------------------------------------------------------------------- *)
(* Setting up goals and terminating them in a theorem.                       *)
(* ------------------------------------------------------------------------- *)

let set_goal p =
  let chk th = if concl th = p then th else failwith "wrong theorem" in
  Goals([[],p],fun [th] -> chk(modusponens th truth));;

let extract_thm gls =
  match gls with
    Goals([],jfn) -> jfn []
  | _ -> failwith "extract_thm: unsolved goals";;

let tac_proof g prf = extract_thm(itlist (fun f -> f) (rev prf) g);;

let prove p prf = tac_proof (set_goal p) prf;;

(* ------------------------------------------------------------------------- *)
(* Conjunction introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

let conj_intro_tac (Goals((asl,And(p,q))::gls,jfn)) =
  let jfn' (thp::thq::ths) =
    jfn(imp_trans_chain [thp; thq] (and_pair p q)::ths) in
  Goals((asl,p)::(asl,q)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* Handy idiom for tactic that does not split subgoals.                      *)
(* ------------------------------------------------------------------------- *)

let jmodify jfn tfn (th::oths) = jfn(tfn th :: oths);;

(* ------------------------------------------------------------------------- *)
(* Version of gen_right with a bound variable change.                        *)
(* ------------------------------------------------------------------------- *)

let gen_right_alpha y x th =
  let th1 = gen_right y th in
  imp_trans th1 (alpha x (consequent(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Universal introduction.                                                   *)
(* ------------------------------------------------------------------------- *)

let forall_intro_tac y (Goals((asl,(Forall(x,p) as fm))::gls,jfn)) =
  if mem y (fv fm) or exists (mem y ** fv ** snd) asl
  then failwith "fix: variable already free in goal" else
  Goals((asl,subst(x |=> Var y) p)::gls,
        jmodify jfn (gen_right_alpha y x));;

(* ------------------------------------------------------------------------- *)
(* Another inference rule: |- P[t] ==> exists x. P[x]                        *)
(* ------------------------------------------------------------------------- *)

let right_exists x t p =
  let th = contrapos(ispec t (Forall(x,Not p))) in
  let Not(Not p') = antecedent(concl th) in
  end_itlist imp_trans
   [imp_contr p' False; imp_add_concl False (iff_imp1 (axiom_not p'));
    iff_imp2(axiom_not (Not p')); th; iff_imp2(axiom_exists x p)];;

(* ------------------------------------------------------------------------- *)
(* Existential introduction.                                                 *)
(* ------------------------------------------------------------------------- *)

let exists_intro_tac t (Goals((asl,Exists(x,p))::gls,jfn)) =
  Goals((asl,subst(x |=> t) p)::gls,
        jmodify jfn (fun th -> imp_trans th (right_exists x t p)));;

(* ------------------------------------------------------------------------- *)
(* Implication introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

let imp_intro_tac s (Goals((asl,Imp(p,q))::gls,jfn)) =
  let jmod = if asl = [] then add_assum True else imp_swap ** shunt in
  Goals(((s,p)::asl,q)::gls,jmodify jfn jmod);;

(* ------------------------------------------------------------------------- *)
(* Append contextual hypothesis to unconditional theorem.                    *)
(* ------------------------------------------------------------------------- *)

let assumptate (Goals((asl,w)::gls,jfn)) th =
  add_assum (list_conj (map snd asl)) th;;

(* ------------------------------------------------------------------------- *)
(* Get the first assumption (quicker than head of assumps result).           *)
(* ------------------------------------------------------------------------- *)

let firstassum asl =
  let p = snd(hd asl) and q = list_conj(map snd (tl asl)) in
  if tl asl = [] then imp_refl p else and_left p q;;

(* ------------------------------------------------------------------------- *)
(* Import "external" theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let using ths p g =
  let ths' = map (fun th -> itlist gen (fv(concl th)) th) ths in
  map (assumptate g) ths';;

(* ------------------------------------------------------------------------- *)
(* Turn assumptions p1,...,pn into theorems |- p1 /\ ... /\ pn ==> pi        *)
(* ------------------------------------------------------------------------- *)

let rec assumps asl =
  match asl with
    [] -> []
  | [l,p] -> [l,imp_refl p]
  | (l,p)::lps ->
        let ths = assumps lps in
        let q = antecedent(concl(snd(hd ths))) in
        let rth = and_right p q in
        (l,and_left p q)::map (fun (l,th) -> l,imp_trans rth th) ths;;

(* ------------------------------------------------------------------------- *)
(* Produce canonical theorem from list of theorems or assumption labels.     *)
(* ------------------------------------------------------------------------- *)

let by hyps p (Goals((asl,w)::gls,jfn)) =
  let ths = assumps asl in map (fun s -> assoc s ths) hyps;;

(* ------------------------------------------------------------------------- *)
(* Main automatic justification step.                                        *)
(* ------------------------------------------------------------------------- *)

let justify byfn hyps p g =
  match byfn hyps p g with
    [th] when consequent(concl th) = p -> th
  | ths ->
      let th = lcffol(itlist (mk_imp ** consequent ** concl) ths p) in
      if ths = [] then assumptate g th else imp_trans_chain ths th;;

(* ------------------------------------------------------------------------- *)
(* Nested subproof.                                                          *)
(* ------------------------------------------------------------------------- *)

let proof tacs p (Goals((asl,w)::gls,jfn)) =
  [tac_proof (Goals([asl,p],fun [th] -> th)) tacs];;

(* ------------------------------------------------------------------------- *)
(* Trivial justification, producing no hypotheses.                           *)
(* ------------------------------------------------------------------------- *)

let at once p gl = [] and once = [];;

(* ------------------------------------------------------------------------- *)
(* Hence an automated terminal tactic.                                       *)
(* ------------------------------------------------------------------------- *)

let auto_tac byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let th = justify byfn hyps w g in
  Goals(gls,fun ths -> jfn(th::ths));;

(* ------------------------------------------------------------------------- *)
(* A "lemma" tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let lemma_tac s p byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let tr = imp_trans(justify byfn hyps p g) in
  let mfn = if asl = [] then tr else imp_unduplicate ** tr ** shunt in
  Goals(((s,p)::asl,w)::gls,jmodify jfn mfn);;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for existential quantification.                        *)
(* ------------------------------------------------------------------------- *)

let exists_elim_tac l fm byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let Exists(x,p) = fm in
  if exists (mem x ** fv) (w::map snd asl)
  then failwith "exists_elim_tac: variable free in assumptions" else
  let th = justify byfn hyps (Exists(x,p)) g in
  let jfn' pth =
    imp_unduplicate(imp_trans th (exists_left x (shunt pth))) in
  Goals(((l,p)::asl,w)::gls,jmodify jfn jfn');;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> r and |- q ==> r then |- p \/ q ==> r                         *)
(* ------------------------------------------------------------------------- *)

let ante_disj th1 th2 =
  let p,r = dest_imp(concl th1) and q,s = dest_imp(concl th2) in
  let ths = map contrapos [th1; th2] in
  let th3 = imp_trans_chain ths (and_pair (Not p) (Not q)) in
  let th4 = contrapos(imp_trans (iff_imp2(axiom_not r)) th3) in
  let th5 = imp_trans (iff_imp1(axiom_or p q)) th4 in
  right_doubleneg(imp_trans th5 (iff_imp1(axiom_not(Imp(r,False)))));;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for disjunction.                                       *)
(* ------------------------------------------------------------------------- *)

let disj_elim_tac l fm byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let th = justify byfn hyps fm g and Or(p,q) = fm in
  let jfn' (pth::qth::ths) =
    let th1 = imp_trans th (ante_disj (shunt pth) (shunt qth)) in
    jfn(imp_unduplicate th1::ths) in
  Goals(((l,p)::asl,w)::((l,q)::asl,w)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

(*
let g0 = set_goal
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>;;

let g1 = imp_intro_tac "ant" g0;;

let g2 = conj_intro_tac g1;;

let g3 = funpow 2 (auto_tac by ["ant"]) g2;;

extract_thm g3;;

(* ------------------------------------------------------------------------- *)
(* All packaged up together.                                                 *)
(* ------------------------------------------------------------------------- *)

prove <<(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
            (forall x y. x <= y ==> g(x) <= g(y))>>
      [imp_intro_tac "ant";
       conj_intro_tac;
       auto_tac by ["ant"];
       auto_tac by ["ant"]];;
*)

(* ------------------------------------------------------------------------- *)
(* Declarative proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let multishunt i th =
  let th1 = imp_swap(funpow i (imp_swap ** shunt) th) in
  imp_swap(funpow (i-1) (unshunt ** imp_front 2) th1);;

let assume lps (Goals((asl,Imp(p,q))::gls,jfn)) =
  if end_itlist mk_and (map snd lps) <> p then failwith "assume" else
  let jfn' th = if asl = [] then add_assum True th
                else multishunt (length lps) th in
  Goals((lps@asl,q)::gls,jmodify jfn jfn');;

let note (l,p) = lemma_tac l p;;

let have p = note("",p);;

let so tac arg byfn =
  tac arg (fun hyps p (Goals((asl,w)::_,_) as gl) ->
                     firstassum asl :: byfn hyps p gl);;

let fix = forall_intro_tac;;

let consider (x,p) = exists_elim_tac "" (Exists(x,p));;

let take = exists_intro_tac;;

let cases = disj_elim_tac "";;

(* ------------------------------------------------------------------------- *)
(* Thesis modification.                                                      *)
(* ------------------------------------------------------------------------- *)

let conclude p byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  let th = justify byfn hyps p gl in
  if p = w then Goals((asl,True)::gls,jmodify jfn (fun _ -> th)) else
  let p',q = dest_and w in
  if p' <> p then failwith "conclude: bad conclusion" else
  let mfn th' = imp_trans_chain [th; th'] (and_pair p q) in
  Goals((asl,q)::gls,jmodify jfn mfn);;

(* ------------------------------------------------------------------------- *)
(* A useful shorthand for solving the whole goal.                            *)
(* ------------------------------------------------------------------------- *)

let our thesis byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  conclude w byfn hyps gl
and thesis = "";;

(* ------------------------------------------------------------------------- *)
(* Termination.                                                              *)
(* ------------------------------------------------------------------------- *)

let qed (Goals((asl,w)::gls,jfn) as gl) =
  if w = True then Goals(gls,fun ths -> jfn(assumptate gl truth :: ths))
  else failwith "qed: non-trivial goal";;

(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

(*
let ewd954 = prove
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
*)

(* ------------------------------------------------------------------------- *)
(* More examples not in the main text.                                       *)
(* ------------------------------------------------------------------------- *)

(*
prove
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
prove
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

prove <<p(a) ==> (forall x. p(x) ==> p(f(x)))
        ==> exists y. p(y) /\ p(f(y))>>
      [our thesis at once;
       qed];;

prove
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

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       so our thesis by ["C"; "A"];
       qed];;

prove <<p(c) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       our thesis by ["A"; "B"];
       qed];;

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"];
       qed];;

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       note ("D",<<p(c)>>) by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"; "D"];
       qed];;


prove <<(p(a) \/ p(b)) ==> q ==> exists y. p(y)>>
  [assume ["A",<<p(a) \/ p(b)>>];
   assume ["",<<q>>];
   cases <<p(a) \/ p(b)>> by ["A"];
     take <<|a|>>;
     so our thesis at once;
     qed;

     take <<|b|>>;
     so our thesis at once;
     qed];;

prove
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

prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   consider ("a",<<p(a)>>) by ["A"];
   so note ("concl",<<p(f(a))>>) by ["B"];
   take <<|a|>>;
   our thesis by ["concl"];
   qed];;

prove <<(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
       ==> (p(a) <=> q(a))>>
  [assume ["A",<<forall x. p(x) ==> q(x)>>];
   assume ["B",<<forall x. q(x) ==> p(x)>>];
   note ("von",<<p(a) ==> q(a)>>) by ["A"];
   note ("bis",<<q(a) ==> p(a)>>) by ["B"];
   our thesis by ["von"; "bis"];
   qed];;

(*** Mizar-like

prove
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

*)

(* ------------------------------------------------------------------------- *)
(* Some amusing efficiency tests versus a "direct" spec.                     *)
(* ------------------------------------------------------------------------- *)

(*****

let test n = gen "x"

let double_th th =
  let tm = concl th in modusponens (modusponens (and_pair tm tm) th) th;;

let testcase n =
  gen "x" (funpow n double_th (lcftaut <<p(x) ==> q(1) \/ p(x)>>));;

let test n = time (spec <<|2|>>) (testcase n),
             time (subst ("x" |=> <<|2|>>)) (concl(testcase n));
             ();;

test 10;;
test 11;;
test 12;;
test 13;;
test 14;;
test 15;;

****)
(* ========================================================================= *)
(* Goedel's theorem and relatives.                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Produce numeral in zero-successor form.                                   *)
(* ------------------------------------------------------------------------- *)

let rec numeral n =
  if n =/ Int 0 then Fn("0",[])
  else Fn("S",[numeral(n -/ Int 1)]);;

(* ------------------------------------------------------------------------- *)
(* Map strings to numbers. This is bijective, to avoid certain quibbles.     *)
(* ------------------------------------------------------------------------- *)

let number s =
  itlist (fun i g -> Int(1 + Char.code(String.get s i)) +/ Int 256 */ g)
         (0--(String.length s - 1)) (Int 0);;

(* ------------------------------------------------------------------------- *)
(* Injective pairing function with "pair x y" always nonzero.                *)
(* ------------------------------------------------------------------------- *)

let pair x y = (x +/ y) */ (x +/ y) +/ x +/ Int 1;;

(* ------------------------------------------------------------------------- *)
(* Goedel numbering of terms and formulas.                                   *)
(* ------------------------------------------------------------------------- *)

let rec gterm tm =
  match tm with
    Var x -> pair (Int 0) (number x)
  | Fn("0",[]) -> pair (Int 1) (Int 0)
  | Fn("S",[t]) -> pair (Int 2) (gterm t)
  | Fn("+",[s;t]) -> pair (Int 3) (pair (gterm s) (gterm t))
  | Fn("*",[s;t]) -> pair (Int 4) (pair (gterm s) (gterm t))
  | _ -> failwith "gterm: not in the language";;

let rec gform fm =
  match fm with
    False -> pair (Int 0) (Int 0)
  | True -> pair (Int 0) (Int 1)
  | Atom(R("=",[s;t])) -> pair (Int 1) (pair (gterm s) (gterm t))
  | Atom(R("<",[s;t])) -> pair (Int 2) (pair (gterm s) (gterm t))
  | Atom(R("<=",[s;t])) -> pair (Int 3) (pair (gterm s) (gterm t))
  | Not(p) -> pair (Int 4) (gform p)
  | And(p,q) -> pair (Int 5) (pair (gform p) (gform q))
  | Or(p,q) -> pair (Int 6) (pair (gform p) (gform q))
  | Imp(p,q) -> pair (Int 7) (pair (gform p) (gform q))
  | Iff(p,q) -> pair (Int 8) (pair (gform p) (gform q))
  | Forall(x,p) -> pair (Int 9) (pair (number x) (gform p))
  | Exists(x,p) -> pair (Int 10) (pair (number x) (gform p))
  | _ -> failwith "gform: not in the language";;

(* ------------------------------------------------------------------------- *)
(* One explicit example.                                                     *)
(* ------------------------------------------------------------------------- *)

(*
gform <<~(x = 0)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Some more examples of things in or not in the set of true formulas.       *)
(* ------------------------------------------------------------------------- *)

(*
gform <<x = x>>;;
gform <<0 < 0>>;;
*)

(* ------------------------------------------------------------------------- *)
(* The "gnumeral" function.                                                  *)
(* ------------------------------------------------------------------------- *)

let gnumeral n = gterm(numeral n);;

(* ------------------------------------------------------------------------- *)
(* Intuition for the self-referential sentence.                              *)
(* ------------------------------------------------------------------------- *)

let diag s =
  let rec replacex n l =
    match l with
      [] -> if n = 0 then "" else failwith "unmatched quotes"
    | "x"::t when n = 0 -> "`"^s^"'"^replacex n t
    | "`"::t -> "`"^replacex (n + 1) t
    | "'"::t -> "'"^replacex (n - 1) t
    | h::t -> h^replacex n t in
  replacex 0 (explode s);;

(*
diag("p(x)");;
diag("This string is diag(x)");;
*)

let phi = diag("P(diag(x))");;

(* ------------------------------------------------------------------------- *)
(* Pseudo-substitution variant.                                              *)
(* ------------------------------------------------------------------------- *)

let qdiag s = "let `x' be `"^s^"' in "^s;;
let phi = qdiag("P(qdiag(x))");;

(* ------------------------------------------------------------------------- *)
(* Analogous construct in natural language.                                  *)
(* ------------------------------------------------------------------------- *)

(*
diag("The result of substituting the quotation of x for `x' in x \
        has property P");;
*)

(* ------------------------------------------------------------------------- *)
(* Quine from Martin Jambon.                                                 *)
(* ------------------------------------------------------------------------- *)

(fun s -> Printf.printf "%s\n%S\n" s s)
"(fun s -> Printf.printf \"%s\\n%S\\n\" s s)";;

(* ------------------------------------------------------------------------- *)
(* Diagonalization and quasi-diagonalization of formulas.                    *)
(* ------------------------------------------------------------------------- *)

let diag x p = subst (x |=> numeral(gform p)) p;;

let qdiag x p = Exists(x,And(mk_eq (Var x) (numeral(gform p)),p));;

(* ------------------------------------------------------------------------- *)
(* Decider for delta-sentences.                                              *)
(* ------------------------------------------------------------------------- *)

let rec dtermval v tm =
  match tm with
    Var x -> apply v x
  | Fn("0",[]) -> Int 0
  | Fn("S",[t]) -> dtermval v t +/ Int 1
  | Fn("+",[s;t]) -> dtermval v s +/ dtermval v t
  | Fn("*",[s;t]) -> dtermval v s */ dtermval v t
  | _ -> failwith "dtermval: not a ground term of the language";;

let rec dholds v fm =
  match fm with
    False -> false
  | True -> true
  | Atom(R("=",[s;t])) -> dtermval v s = dtermval v t
  | Atom(R("<",[s;t])) -> dtermval v s </ dtermval v t
  | Atom(R("<=",[s;t])) -> dtermval v s <=/ dtermval v t
  | Not(p) -> not(dholds v p)
  | And(p,q) -> dholds v p & dholds v q
  | Or(p,q) -> dholds v p or dholds v q
  | Imp(p,q) -> not(dholds v p) or dholds v q
  | Iff(p,q) -> dholds v p = dholds v q
  | Forall(x,Imp(Atom(R(a,[Var y;t])),p)) -> dhquant forall v x y a t p
  | Exists(x,And(Atom(R(a,[Var y;t])),p)) -> dhquant exists v x y a t p
  | _ -> failwith "dholds: not an arithmetical delta-formula"
and dhquant pred v x y a t p =
  if x <> y or mem x (fvt t) then failwith "dholds: not delta" else
  let m = if a = "<" then dtermval v t -/ Int 1 else dtermval v t in
  pred (fun n -> dholds ((x |-> n) v) p) (Int 0 --- m);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let prime_form p = subst("p" |=> numeral(Int p))
 <<S(S(0)) <= p /\
   forall n. n < p ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)>>;;

dholds undefined (prime_form 100);;
dholds undefined (prime_form 101);;
*)

(* ------------------------------------------------------------------------- *)
(* Test sigma/pi status (don't check the language of arithmetic).            *)
(* ------------------------------------------------------------------------- *)

type formulaclass = Sigma | Pi | Delta;;

let opp = function Sigma -> Pi | Pi -> Sigma | Delta -> Delta;;

let rec classify c n fm =
  match fm with
    False | True | Atom(_) -> true
  | Not p -> classify (opp c) n p
  | And(p,q) | Or(p,q) -> classify c n p & classify c n q
  | Imp(p,q) -> classify (opp c) n p & classify c n q
  | Iff(p,q) -> classify Delta n p & classify Delta n q
  | Exists(x,p) when n <> 0 & c = Sigma -> classify c n p
  | Forall(x,p) when n <> 0 & c = Pi -> classify c n p
  | (Exists(x,And(Atom(R(("<"|"<="),[Var y;t])),p))|
     Forall(x,Imp(Atom(R(("<"|"<="),[Var y;t])),p)))
       when x = y & not(mem x (fvt t)) -> classify c n p
  | Exists(x,p) |  Forall(x,p) -> n <> 0 & classify (opp c) (n - 1) fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
classify Sigma 1
  <<forall x. x < 2
              ==> exists y z. forall w. w < x + 2
                                        ==> w + x + y + z = 42>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Verification of true Sigma_1 formulas, refutation of false Pi_1 formulas. *)
(* ------------------------------------------------------------------------- *)

let rec veref sign m v fm =
  match fm with
    False -> sign false
  | True -> sign true
  | Atom(R("=",[s;t])) -> sign(dtermval v s = dtermval v t)
  | Atom(R("<",[s;t])) -> sign(dtermval v s </ dtermval v t)
  | Atom(R("<=",[s;t])) -> sign(dtermval v s <=/ dtermval v t)
  | Not(p) -> veref (not ** sign) m v p
  | And(p,q) -> sign(sign(veref sign m v p) & sign(veref sign m v q))
  | Or(p,q) -> sign(sign(veref sign m v p) or sign(veref sign m v q))
  | Imp(p,q) -> veref sign m v (Or(Not p,q))
  | Iff(p,q) -> veref sign m v (And(Imp(p,q),Imp(q,p)))
  | Exists(x,p) when sign true
        -> exists (fun n -> veref sign m ((x |-> n) v) p) (Int 0---m)
  | Forall(x,p) when sign false
        -> exists (fun n -> veref sign m ((x |-> n) v) p) (Int 0---m)
  | Forall(x,Imp(Atom(R(a,[Var y;t])),p)) when sign true
        -> verefboundquant m v x y a t sign p
  | Exists(x,And(Atom(R(a,[Var y;t])),p)) when sign false
        -> verefboundquant m v x y a t sign p

and verefboundquant m v x y a t sign p =
  if x <> y or mem x (fvt t) then failwith "veref" else
  let m = if a = "<" then dtermval v t -/ Int 1 else dtermval v t in
  forall (fun n -> veref sign m ((x |-> n) v) p) (Int 0 --- m);;

let sholds = veref (fun b -> b);;

(* ------------------------------------------------------------------------- *)
(* Find adequate bound for all existentials to make sentence true.           *)
(* ------------------------------------------------------------------------- *)

let sigma_bound fm = first (Int 0) (fun n -> sholds n undefined fm);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
sigma_bound
  <<exists p x.
     p < x /\
     (S(S(0)) <= p /\
      forall n. n < p
                ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)) /\
     ~(x = 0) /\
     forall z. z <= x
               ==> (exists w. w <= x /\ x = z * w)
                   ==> z = S(0) \/ exists x. x <= z /\ z = p * x>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Turing machines.                                                          *)
(* ------------------------------------------------------------------------- *)

type symbol = Blank | One;;

type direction = Left | Right | Stay;;

(* ------------------------------------------------------------------------- *)
(* Type of the tape.                                                         *)
(* ------------------------------------------------------------------------- *)

type tape = Tape of int * (int,symbol)func;;

(* ------------------------------------------------------------------------- *)
(* Look at current character.                                                *)
(* ------------------------------------------------------------------------- *)

let look (Tape(r,f)) = tryapplyd f r Blank;;

(* ------------------------------------------------------------------------- *)
(* Write a symbol on the tape.                                               *)
(* ------------------------------------------------------------------------- *)

let write s (Tape(r,f)) = Tape (r,(r |-> s) f);;

(* ------------------------------------------------------------------------- *)
(* Move machine left or right.                                               *)
(* ------------------------------------------------------------------------- *)

let move dir (Tape(r,f)) =
  let d = if dir = Left then -1 else if dir = Right then 1 else 0 in
  Tape(r+d,f);;

(* ------------------------------------------------------------------------- *)
(* Configurations, i.e. state and tape together.                             *)
(* ------------------------------------------------------------------------- *)

type config = Config of int * tape;;

(* ------------------------------------------------------------------------- *)
(* Keep running till we get to an undefined state.                           *)
(* ------------------------------------------------------------------------- *)

let rec run prog (Config(state,tape) as config) =
  let stt = (state,look tape) in
  if defined prog stt then
    let char,dir,state' = apply prog stt in
    run prog (Config(state',move dir (write char tape)))
  else config;;

(* ------------------------------------------------------------------------- *)
(* Tape with set of canonical input arguments.                               *)
(* ------------------------------------------------------------------------- *)

let input_tape =
  let writen n =
    funpow n (move Left ** write One) ** move Left ** write Blank in
  fun args -> itlist writen args (Tape(0,undefined));;

(* ------------------------------------------------------------------------- *)
(* Read the result of the tape.                                              *)
(* ------------------------------------------------------------------------- *)

let rec output_tape tape =
  let tape' = move Right tape in
  if look tape' = Blank then 0
  else 1 + output_tape tape';;

(* ------------------------------------------------------------------------- *)
(* Overall program execution.                                                *)
(* ------------------------------------------------------------------------- *)

let exec prog args =
  let c = Config(1,input_tape args) in
  let Config(_,t) = run prog c in
  output_tape t;;

(* ------------------------------------------------------------------------- *)
(* Example program (successor).                                              *)
(* ------------------------------------------------------------------------- *)

(*
let prog_suc = itlist (fun m -> m)
 [(1,Blank) |-> (Blank,Right,2);
  (2,One) |-> (One,Right,2);
  (2,Blank) |-> (One,Right,3);
  (3,Blank) |-> (Blank,Left,4);
  (3,One) |-> (Blank,Left,4);
  (4,One) |-> (One,Left,4);
  (4,Blank) |-> (Blank,Stay,0)]
 undefined;;

exec prog_suc [0];;

exec prog_suc [1];;

exec prog_suc [19];;
*)

(* ------------------------------------------------------------------------- *)
(* Robinson axioms.                                                          *)
(* ------------------------------------------------------------------------- *)

let robinson =
 <<(forall m n. S(m) = S(n) ==> m = n) /\
   (forall n. ~(n = 0) <=> exists m. n = S(m)) /\
   (forall n. 0 + n = n) /\
   (forall m n. S(m) + n = S(m + n)) /\
   (forall n. 0 * n = 0) /\
   (forall m n. S(m) * n = n + m * n) /\
   (forall m n. m <= n <=> exists d. m + d = n) /\
   (forall m n. m < n <=> S(m) <= n)>>;;

let [suc_inj; num_cases; add_0; add_suc; mul_0;
     mul_suc; le_def; lt_def] = conjths robinson;;

(* ------------------------------------------------------------------------- *)
(* Particularly useful "right handed" inference rules.                       *)
(* ------------------------------------------------------------------------- *)

let right_spec t th = imp_trans th (ispec t (consequent(concl th)));;

let right_mp ith th =
  imp_unduplicate(imp_trans th (imp_swap ith));;

let right_imp_trans th1 th2 =
  imp_unduplicate(imp_front 2 (imp_trans2 th1 (imp_swap th2)));;

let right_sym th =
  let s,t = dest_eq(consequent(concl th)) in imp_trans th (eq_sym s t);;

let right_trans th1 th2 =
  let s,t = dest_eq(consequent(concl th1))
  and t',u = dest_eq(consequent(concl th2)) in
  imp_trans_chain [th1; th2] (eq_trans s t u);;

(* ------------------------------------------------------------------------- *)
(* Evalute constant expressions (allow non-constant on RHS in last clause).  *)
(* ------------------------------------------------------------------------- *)

let rec robop tm =
  match tm with
    Fn(op,[Fn("0",[]);t]) ->
        if op = "*" then right_spec t mul_0
        else right_trans (right_spec t add_0) (robeval t)
  | Fn(op,[Fn("S",[u]);t]) ->
        let th1 = if op = "+" then add_suc else mul_suc in
        let th2 = itlist right_spec [t;u] th1 in
        right_trans th2 (robeval (rhs(consequent(concl th2))))

and robeval tm =
  match tm with
    Fn("S",[t]) ->
        let th = robeval t in
        let t' = rhs(consequent(concl th)) in
        imp_trans th (axiom_funcong "S" [t] [t'])
  | Fn(op,[s;t]) ->
        let th1 = robeval s in
        let s' = rhs(consequent(concl th1)) in
        let th2 = robop (Fn(op,[s';t])) in
        let th3 = axiom_funcong op [s;t] [s';t] in
        let th4 = modusponens (imp_swap th3) (axiom_eqrefl t) in
        right_trans (imp_trans th1 th4) th2
  | _ -> add_assum robinson (axiom_eqrefl tm);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

(*
robeval <<|S(0) + (S(S(0)) * ((S(0) + S(S(0)) + S(0))))|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Consequences of the axioms.                                               *)
(* ------------------------------------------------------------------------- *)

let robinson_consequences =
 <<(forall n. S(n) = 0 ==> false) /\
   (forall n. 0 = S(n) ==> false) /\
   (forall m n. (m = n ==> false) ==> (S(m) = S(n) ==> false)) /\
   (forall m n. (exists d. m + d = n) ==> m <= n) /\
   (forall m n. S(m) <= n ==> m < n) /\
   (forall m n. (forall d. d <= n ==> d = m ==> false)
                ==> m <= n ==> false) /\
   (forall m n. (forall d. d < n ==> d = m ==> false)
                ==> m < n ==> false) /\
   (forall n. n <= 0 \/ exists m. S(m) = n) /\
   (forall n. n <= 0 ==> n = 0) /\
   (forall m n. S(m) <= S(n) ==> m <= n) /\
   (forall m n. m < S(n) ==> m <= n) /\
   (forall n. n < 0 ==> false)>>;;

let robinson_thm =
  prove (Imp(robinson,robinson_consequences))
  [note("eq_refl",<<forall x. x = x>>) using [axiom_eqrefl (Var "x")];
   note("eq_trans",<<forall x y z. x = y ==> y = z ==> x = z>>)
      using [eq_trans (Var "x") (Var "y") (Var "z")];
   note("eq_sym",<<forall x y. x = y ==> y = x>>)
      using [eq_sym (Var "x") (Var "y")];
   note("suc_cong",<<forall a b. a = b ==> S(a) = S(b)>>)
      using [axiom_funcong "S" [Var "a"] [Var "b"]];
   note("add_cong",
        <<forall a b c d. a = b /\ c = d ==> a + c = b + d>>)
      using [axiom_funcong "+" [Var "a"; Var "c"] [Var "b"; Var "d"]];
   note("le_cong",
        <<forall a b c d. a = b /\ c = d ==> a <= c ==> b <= d>>)
      using [axiom_predcong "<=" [Var "a"; Var "c"] [Var "b"; Var "d"]];
   note("lt_cong",
        <<forall a b c d. a = b /\ c = d ==> a < c ==> b < d>>)
      using [axiom_predcong "<" [Var "a"; Var "c"] [Var "b"; Var "d"]];

   assume ["suc_inj",<<forall m n. S(m) = S(n) ==> m = n>>;
           "num_nz",<<forall n. ~(n = 0) <=> exists m. n = S(m)>>;
           "add_0",<<forall n. 0 + n = n>>;
           "add_suc",<<forall m n. S(m) + n = S(m + n)>>;
           "mul_0",<<forall n. 0 * n = 0>>;
           "mul_suc",<<forall m n. S(m) * n = n + m * n>>;
           "le_def",<<forall m n. m <= n <=> exists d. m + d = n>>;
           "lt_def",<<forall m n. m < n <=> S(m) <= n>>];
   note("not_suc_0",<<forall n. ~(S(n) = 0)>>) by ["num_nz"; "eq_refl"];
   so conclude <<forall n. S(n) = 0 ==> false>> at once;
   so conclude <<forall n. 0 = S(n) ==> false>> by ["eq_sym"];
   note("num_cases",<<forall n. (n = 0) \/ exists m. n = S(m)>>)
         by ["num_nz"];
   note("suc_inj_eq",<<forall m n. S(m) = S(n) <=> m = n>>)
     by ["suc_inj"; "suc_cong"];
   so conclude
     <<forall m n. (m = n ==> false) ==> (S(m) = S(n) ==> false)>>
     at once;
   conclude <<forall m n. (exists d. m + d = n) ==> m <= n>>
     by ["le_def"];
   conclude <<forall m n. S(m) <= n ==> m < n>> by ["lt_def"];
   conclude <<forall m n. (forall d. d <= n ==> d = m ==> false)
                          ==> m <= n ==> false>>
     by ["eq_refl"; "le_cong"];
   conclude <<forall m n. (forall d. d < n ==> d = m ==> false)
                          ==> m < n ==> false>>
     by ["eq_refl"; "lt_cong"];
   have <<0 <= 0>> by ["le_def"; "add_0"];
   so have <<forall x. x = 0 ==> x <= 0>>
     by ["le_cong"; "eq_refl"; "eq_sym"];
   so conclude <<forall n. n <= 0 \/ (exists m. S(m) = n)>>
     by ["num_nz"; "eq_sym"];
   note("add_eq_0",<<forall m n. m + n = 0 ==> m = 0 /\ n = 0>>) proof
    [fix "m"; fix "n";
     assume ["A",<<m + n = 0>>];
     cases <<m = 0 \/ exists p. m = S(p)>> by ["num_cases"];
       so conclude <<m = 0>> at once;
       so have <<m + n = 0 + n>> by ["add_cong"; "eq_refl"];
       so our thesis by ["A"; "add_0"; "eq_sym"; "eq_trans"];
     qed;
       so consider ("p",<<m = S(p)>>) at once;
       so have <<m + n = S(p) + n>> by ["add_cong"; "eq_refl"];
       so have <<m + n = S(p + n)>> by ["eq_trans"; "add_suc"];
       so have <<S(p + n) = 0>> by ["A"; "eq_sym"; "eq_trans"];
       so our thesis by ["not_suc_0"];
     qed];
   so conclude <<forall n. n <= 0 ==> n = 0>> by ["le_def"];
   have <<forall m n. S(m) <= S(n) ==> m <= n>> proof
    [fix "m"; fix "n";
     assume ["lesuc",<<S(m) <= S(n)>>];
     so consider("d",<<S(m) + d = S(n)>>) by ["le_def"];
     so have <<S(m + d) = S(n)>> by ["add_suc"; "eq_sym"; "eq_trans"];
     so have <<m + d = n>> by ["suc_inj"];
     so conclude <<m <= n>> by ["le_def"];
     qed];
   so conclude <<forall m n. S(m) <= S(n) ==> m <= n>> at once;
   so conclude <<forall m n. m < S(n) ==> m <= n>> by ["lt_def"];
   fix "n";
   assume ["hyp",<<n < 0>>];
   so have <<S(n) <= 0>> by ["lt_def"];
   so consider("d",<<S(n) + d = 0>>) by ["le_def"];
   so have <<S(n + d) = 0>> by ["add_suc"; "eq_trans"; "eq_sym"];
   so our thesis by ["not_suc_0"];
   qed];;

let [suc_0_l; suc_0_r; suc_inj_false;
     expand_le; expand_lt; expand_nle; expand_nlt;
     num_lecases; le_0; le_suc; lt_suc; lt_0] =
    map (imp_trans robinson_thm) (conjths robinson_consequences);;

(* ------------------------------------------------------------------------- *)
(* Prove or disprove equations between ground terms.                         *)
(* ------------------------------------------------------------------------- *)

let rob_eq s t =
  let sth = robeval s and tth = robeval t in
  right_trans sth (right_sym tth);;

let rec rob_nen(s,t) =
  match (s,t) with
      (Fn("S",[s']),Fn("0",[])) -> right_spec s' suc_0_l
    | (Fn("0",[]),Fn("S",[t'])) -> right_spec t' suc_0_r
    | (Fn("S",[u]),Fn("S",[v])) ->
        right_mp (itlist right_spec [v;u] suc_inj_false) (rob_nen(u,v))
    | _ -> failwith "rob_ne: true equation or unexpected term";;

let rob_ne s t =
  let sth = robeval s and tth = robeval t in
  let s' = rhs(consequent(concl sth))
  and t' = rhs(consequent(concl tth)) in
  let th = rob_nen(s',t') in
  let xth = axiom_predcong "=" [s; t] [s'; t'] in
  right_imp_trans (right_mp (imp_trans sth xth) tth) th;;

(*
rob_ne <<|S(0) + S(0) + S(0)|>> <<|S(S(0)) * S(S(0))|>>;;
rob_ne <<|0 + 0 * S(0)|>> <<|S(S(0)) + 0|>>;;
rob_ne <<|S(S(0)) + 0|>> <<|0 + 0 + 0 * 0|>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Dual version of "eliminate_connective" for unnegated case.                *)
(* ------------------------------------------------------------------------- *)

let introduce_connective fm =
  if not(negativef fm) then iff_imp2(expand_connective fm)
  else imp_add_concl False (iff_imp1(expand_connective(negatef fm)));;

(* ------------------------------------------------------------------------- *)
(* This is needed to preserve the canonical form for bounded quantifiers.    *)
(*                                                                           *)
(* |- (forall x. p(x) ==> q(x) ==> false)                                    *)
(*    ==> (exists x. p(x) /\ q(x)) ==> false                                 *)
(* ------------------------------------------------------------------------- *)

let elim_bex fm =
  match fm with
   Imp(Exists(x,And(p,q)),False) ->
        let pq = And(p,q) and pqf = Imp(p,Imp(q,False)) in
        let th1 = imp_swap(imp_refl(Imp(pqf,False))) in
        let th2 = imp_trans th1 (introduce_connective(Imp(pq,False))) in
        imp_trans (genimp x th2) (exists_left_th x pq False)
  | _ -> failwith "elim_bex";;

(* ------------------------------------------------------------------------- *)
(* Eliminate some concepts in terms of others.                               *)
(* ------------------------------------------------------------------------- *)

let sigma_elim fm =
  match fm with
    Atom(R("<=",[s;t])) -> itlist right_spec [t;s] expand_le
  | Atom(R("<",[s;t])) -> itlist right_spec [t;s] expand_lt
  | Imp(Atom(R("<=",[s;t])),False) -> itlist right_spec [t;s] expand_nle
  | Imp(Atom(R("<",[s;t])),False) -> itlist right_spec [t;s] expand_nlt
  | Imp(Exists(x,And(p,q)),False) -> add_assum robinson (elim_bex fm)
  | _ -> add_assum robinson (introduce_connective fm);;

(* ------------------------------------------------------------------------- *)
(* |- R ==> forall x. x <= 0 ==> P(x)  |- R ==> forall x. x <= n ==> P(S(x)) *)
(* ----------------------------------------------------------------------    *)
(*         |- R ==> forall x. x <= S(n) ==> P(x)                             *)
(* ------------------------------------------------------------------------- *)

let boundquant_step th0 th1 =
  match concl th0,concl th1 with
    Imp(_,Forall(x,Imp(_,p))),
          Imp(_,Forall(_,Imp(Atom(R("<=",[_;t])),_))) ->
      let th2 = itlist right_spec [t;Var x] le_suc in
      let th3 = right_imp_trans th2 (right_spec (Var x) th1) in
      let y = variant "y" (var(concl th1)) in
      let q = Imp(Atom(R("<=",[Var x; Fn("S",[t])])),p) in
      let qx = consequent(concl th3) and qy = subst (x |=> Var y) q in
      let th4 = imp_swap(isubst (Fn("S",[Var x])) (Var y) qx qy) in
      let th5 = exists_left x (imp_swap (imp_trans th3 th4)) in
      let th6 = spec (Var x) (gen y th5) in
      let th7 = imp_insert (antecedent q) (right_spec (Var x) th0) in
      let th8 = ante_disj (imp_front 2 th7) th6 in
      let th9 = right_spec (Var x) num_lecases in
      let a1 = consequent(concl th9) and a2 = antecedent(concl th8) in
      let tha = modusponens (isubst zero zero a1 a2)
                            (axiom_eqrefl zero) in
      gen_right x (imp_unduplicate(imp_trans (imp_trans th9 tha) th8));;

(* ------------------------------------------------------------------------- *)
(* Main sigma-prover.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec sigma_prove fm =
  match fm with
    False -> failwith "sigma_prove"
  | Atom(R("=",[s;t])) -> rob_eq s t
  | Imp(Atom(R("=",[s;t])),False) -> rob_ne s t
  | Imp(p,q) when p = q -> add_assum robinson (imp_refl p)
  | Imp(Imp(p,q),False) ->
        let pth = sigma_prove p and qth = sigma_prove (Imp(q,False)) in
        right_mp (imp_trans qth (imp_truefalse p q)) pth
  | Imp(p,q) when q <> False ->
        let m = sigma_bound fm in
        if sholds m undefined q then imp_insert p (sigma_prove q)
        else imp_trans2 (sigma_prove (Imp(p,False))) (ex_falso q)
  | Imp(Forall(x,p),False) ->
        let m = sigma_bound (Exists(x,Not p)) in
        let n = first (Int 0) (fun n ->
          sholds m undefined (subst (x |=> numeral n) (Not p))) in
        let ith = ispec (numeral n) (Forall(x,p)) in
        let th = sigma_prove (Imp(consequent(concl ith),False)) in
        imp_swap(imp_trans ith (imp_swap th))
  | Forall(x,Imp(Atom(R(("<="|"<" as a),[Var x';t])),q))
        when x' = x & not(occurs_in (Var x) t) -> bounded_prove(a,x,t,q)
  | _ -> let th = sigma_elim fm in
         right_mp th (sigma_prove (antecedent(consequent(concl th))))

(* ------------------------------------------------------------------------- *)
(* Evaluate the bound for a bounded quantifier                               *)
(* ------------------------------------------------------------------------- *)

and bounded_prove(a,x,t,q) =
  let tth = robeval t in
  let u = rhs(consequent(concl tth)) in
  let th1 = boundednum_prove(a,x,u,q)
  and th2 = axiom_predcong a [Var x;t] [Var x;u] in
  let th3 = imp_trans tth (modusponens th2 (axiom_eqrefl (Var x))) in
  let a,b = dest_imp(consequent(concl th3)) in
  let th4 = imp_swap(imp_trans_th a b q) in
  gen_right x (right_mp (imp_trans th3 th4) (right_spec (Var x) th1))

(* ------------------------------------------------------------------------- *)
(* Actual expansion of a bounded quantifier.                                 *)
(* ------------------------------------------------------------------------- *)

and boundednum_prove(a,x,t,q) =
  match a,t with
    "<",Fn("0",[]) ->
        gen_right x (imp_trans2 (right_spec (Var x) lt_0) (ex_falso q))
  | "<",Fn("S",[u]) ->
        let th1 = itlist right_spec [u;Var x] lt_suc in
        let th2 = boundednum_prove("<=",x,u,q) in
        let th3 = imp_trans2 th1 (imp_swap(right_spec (Var x) th2)) in
        gen_right x (imp_unduplicate(imp_front 2 th3))
  | "<=",Fn("0",[]) ->
        let q' = subst (x |=> zero) q in
        let th1 = imp_trans (eq_sym (Var x) zero)
                            (isubst zero (Var x) q' q) in
        let th2 = imp_trans2 (right_spec (Var x) le_0) th1 in
        let th3 = imp_swap(imp_front 2 th2) in
        gen_right x (right_mp th3 (sigma_prove q'))
  | "<=",Fn("S",[u]) ->
        let fm' = Forall(x,Imp(Atom(R("<=",[Var x;zero])),q))
        and fm'' = Forall(x,Imp(Atom(R("<=",[Var x;u])),
                                subst (x |=> Fn("S",[Var x])) q)) in
        boundquant_step (sigma_prove fm') (sigma_prove fm'');;

(* ------------------------------------------------------------------------- *)
(* Example in the text.                                                      *)
(* ------------------------------------------------------------------------- *)

(*
sigma_prove
  <<exists p.
      S(S(0)) <= p /\
      forall n. n < p
                ==> (exists x. x <= p /\ p = n * x) ==> n = S(0)>>;;
*)

(* ------------------------------------------------------------------------- *)
(* The essence of Goedel's first theorem.                                    *)
(* ------------------------------------------------------------------------- *)

(*
meson
 <<(True(G) <=> ~(|--(G))) /\ Pi(G) /\
   (forall p. Sigma(p) ==> (|--(p) <=> True(p))) /\
   (forall p. True(Not(p)) <=> ~True(p)) /\
   (forall p. Pi(p) ==> Sigma(Not(p)))
   ==> (|--(Not(G)) <=> |--(G))>>;;
*)

(* ------------------------------------------------------------------------- *)
(* Godel's second theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
let godel_2 = prove
 <<(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
   (forall p. |--(imp(Pr(p),Pr(Pr(p)))))
   ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
       (forall p q. |--(imp(q,imp(p,q)))) /\
       (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))))
       ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G))
           ==> |--(imp(Pr(F),F)) ==> |--(F)>>
 [assume["lob1",<<forall p. |--(p) ==> |--(Pr(p))>>;
         "lob2",<<forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))>>;
         "lob3",<<forall p. |--(imp(Pr(p),Pr(Pr(p))))>>];
  assume["logic",<<(forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
                   (forall p q. |--(imp(q,imp(p,q)))) /\
                   (forall p q r. |--(imp(imp(p,imp(q,r)),
                                      imp(imp(p,q),imp(p,r)))))>>];
  assume ["fix1",<<|--(imp(G,imp(Pr(G),F)))>>;
          "fix2",<<|--(imp(imp(Pr(G),F),G))>>];
  assume["consistency",<<|--(imp(Pr(F),F))>>];
  have <<|--(Pr(imp(G,imp(Pr(G),F))))>> by ["lob1"; "fix1"];
  so have <<|--(imp(Pr(G),Pr(imp(Pr(G),F))))>> by ["lob2"; "logic"];
  so have <<|--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))>> by ["lob2"; "logic"];
  so have <<|--(imp(Pr(G),Pr(F)))>> by ["lob3"; "logic"];
  so note("L",<<|--(imp(Pr(G),F))>>) by ["consistency"; "logic"];
  so have <<|--(G)>> by ["fix2"; "logic"];
  so have <<|--(Pr(G))>> by ["lob1"; "logic"];
  so conclude <<|--(F)>> by ["L"; "logic"];
  qed];;
*)
