(**************************************************************

Copyright (c) 2015, Anders Schlichtkrull and Jørgen Villadsen
All rights reserved. (See "LICENSE" for details.)

 **************************************************************)

(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Pierre Weis, projet Cristal, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Library functions *)
val max_int = 
    case Int.maxInt of
      SOME n => n
	| NONE => 1073741823
;;

fun max a b = Int.max(a,b);;

fun string_make n c =
	if n<0 then raise Fail "n<0" else
	let fun string_make_aux s n' =
	  if n' = 0 then s else string_make_aux (c::s) (n'-1)
	in
	String.implode (string_make_aux [] n)
	end
;;

fun pred x = x - 1;;

(* Different from OCaml version in that it does not throw Invalid_argument exception *)
fun output oc buf pos len =
  TextIO.output(oc,String.substring(buf,pos,len));;

(* A pretty-printing facility and definition of formatters for ``parallel''
   (i.e. unrelated or independent) pretty-printing on multiple out channels. *)

(**************************************************************

  Data structures definitions.

 **************************************************************)

type size = int;;
fun  size_of_int (n : int)  = (n : size);;
fun  int_of_size (s : size) = (s : int);;

(* Tokens are one of the following : *)

type tag = string

datatype pp_token =
  Pp_text of string            (* normal text *)
| Pp_break of int * int        (* complete break *)
| Pp_tbreak of int * int       (* go to next tabulation *)
| Pp_stab                      (* set a tabulation *)
| Pp_begin of int * block_type (* beginning of a block *)
| Pp_end                       (* end of a block *)
| Pp_tbegin of tblock          (* beginning of a tabulation block *)
| Pp_tend                      (* end of a tabulation block *)
| Pp_newline                   (* to force a newline inside a block *)
| Pp_if_newline                (* to do something only if this very
                                  line has been broken *)
| Pp_open_tag of string        (* opening a tag name *)
| Pp_close_tag                 (* closing the most recently opened tag *)

and block_type =
  Pp_hbox   (* Horizontal block no line breaking *)
| Pp_vbox   (* Vertical block each break leads to a new line *)
| Pp_hvbox  (* Horizontal-vertical block: same as vbox, except if this block
               is small enough to fit on a single line *)
| Pp_hovbox (* Horizontal or Vertical block: breaks lead to new line
               only when necessary to print the content of the block *)
| Pp_box    (* Horizontal or Indent block: breaks lead to new line
               only when necessary to print the content of the block, or
               when it leads to a new indentation of the current line *)
| Pp_fits   (* Internal usage: when a block fits on a single line *)

and tblock =
    Pp_tbox of int list ref  (* Tabulation box *)
;;

fun  string_of_tag (t : tag)  = (t : string);;
fun  tag_of_string (s : string)  = (s : tag);;

(* The Queue:
   contains all formatting elements.
   elements are tuples (size, token, length), where
   size is set when the size of the block is known
   len is the declared length of the token. *)
type pp_queue_elem = {
  elem_size : size ref,
  token : pp_token,
  length : int
};;

(* Scan stack:
   each element is (left_total, queue element) where left_total
   is the value of pp_left_total when the element has been enqueued. *)
datatype pp_scan_elem = Scan_elem of int * pp_queue_elem;;

(* Formatting stack:
   used to break the lines while printing tokens.
   The formatting stack contains the description of
   the currently active blocks. *)
datatype pp_format_elem = Format_elem of block_type * int;;

(* General purpose queues, used in the formatter. *)
datatype 'a queue_elem =
     Nil
   | Cons of 'a queue_cell
and 'a queue_cell = Queue_cell of {
  head : 'a ref,
  tail : ('a queue_elem) ref
};;

fun dest_q_cell (Queue_cell c) = c;;

type 'a queue = {
  insert : ('a queue_elem) ref,
  body : ('a queue_elem) ref
}
;;



(* A formatter with all its machinery. *)
type formatter = {
  pp_scan_stack : (pp_scan_elem list) ref,
  pp_format_stack : (pp_format_elem list) ref,
  pp_tbox_stack : (tblock list) ref,
  pp_tag_stack : (tag list) ref,
  pp_mark_stack : (tag list) ref,
  (* Global variables: default initialization is
     set_margin 78
     set_min_space_left 0. *)
  (* Value of right margin. *)
   pp_margin : int ref,
  (* Minimal space left before margin, when opening a block. *)
   pp_min_space_left : int ref,
  (* Maximum value of indentation:
     no blocks can be opened further. *)
   pp_max_indent : int ref,
  (* Space remaining on the current line. *)
   pp_space_left : int ref,
  (* Current value of indentation. *)
   pp_current_indent : int ref,
  (* True when the line has been broken by the pretty-printer. *)
   pp_is_new_line : bool ref,
  (* Total width of tokens already printed. *)
   pp_left_total : int ref,
  (* Total width of tokens ever put in queue. *)
   pp_right_total : int ref,
  (* Current number of opened blocks. *)
   pp_curr_depth : int ref,
  (* Maximum number of blocks which can be simultaneously opened. *)
   pp_max_boxes : int ref,
  (* Ellipsis string. *)
   pp_ellipsis : string ref,
  (* Output function. *)
   pp_output_function : (string -> int -> int -> unit) ref,
  (* Flushing function. *)
   pp_flush_function : (unit -> unit) ref,
  (* Output of new lines. *)
   pp_output_newline : (unit -> unit) ref,
  (* Output of indentation spaces. *)
   pp_output_spaces : (int -> unit) ref,
  (* Are tags printed ? *)
   pp_print_tags : bool ref,
  (* Are tags marked ? *)
   pp_mark_tags : bool ref,
  (* Find opening and closing markers of tags. *)
   pp_mark_open_tag : (tag -> string) ref,
   pp_mark_close_tag : (tag -> string) ref,
   pp_print_open_tag : (tag -> unit) ref,
   pp_print_close_tag : (tag -> unit) ref,
  (* The pretty-printer queue. *)
   pp_queue : (pp_queue_elem queue) ref
}
;;

(* Queues auxilliaries. *)
fun make_queue () = ({ insert = ref Nil, body = ref Nil }:'a queue);;

fun clear_queue (q : 'a queue) = ((#insert q ) := Nil; (#body q ) := Nil);;

fun add_queue x (q : 'a queue) =
  let val c = Cons (Queue_cell { head = ref x, tail = ref Nil} ) in
  case q of
    { insert = ref (Cons (Queue_cell cell)), body = _} => (
	   #insert q := c; 
	   #tail cell := c
	   )
  (* Invariant: when insert is Nil body should be Nil. *)
  | { insert = ref Nil, body = _ } => (
       #insert q := c; 
	   #body q := c
	   )
  end;;

exception Empty_queue;;

val peek_queue = fn
    { body = ref( Cons ( Queue_cell { head = ref x, tail = _ })), insert = _ } => x
  | { body = ref Nil, insert = _ } => raise Empty_queue
;;

val take_queue = fn
    q as { body = ref (Cons (Queue_cell { head = ref x, tail = ref tl })), insert = _ } => (
    (#body q) := tl;
    if tl = Nil then (#insert q) := Nil else (); (* Maintain the invariant. *)
    x
	)
  | { body = ref Nil, insert = _ } => raise Empty_queue
;;

(* Enter a token in the pretty-printer queue. *)
fun pp_enqueue (state : formatter) (token as { length = len, elem_size = _, token = _}) =(
  #pp_right_total state := !(#pp_right_total state) + len;
  add_queue token (!(#pp_queue state))
);;

fun pp_clear_queue (state : formatter) =(
  (#pp_left_total state ) := 1; (#pp_right_total state ) := 1;
  clear_queue (!(#pp_queue state))
);;

(* Pp_infinity: large value for default tokens size.

   Pp_infinity is documented as being greater than 1e10; to avoid
   confusion about the word ``greater'', we choose pp_infinity greater
   than 1e10 + 1; for correct handling of tests in the algorithm,
   pp_infinity must be even one more than 1e10 + 1; let's stand on the
   safe side by choosing 1.e10+10.

   Pp_infinity could probably be 1073741823 that is 2^30 - 1, that is
   the minimal upper bound for integers; now that max_int is defined,
   this limit could also be defined as max_int - 1.

   However, before setting pp_infinity to something around max_int, we
   must carefully double-check all the integer arithmetic operations
   that involve pp_infinity, since any overflow would wreck havoc the
   pretty-printing algorithm's invariants. Given that this arithmetic
   correctness check is difficult and error prone and given that 1e10
   + 1 is in practice large enough, there is no need to attempt to set
   pp_infinity to the theoretically maximum limit. It is not worth the
   burden ! *)

val pp_infinity = 1000000010;;

(* Output functions for the formatter. *)
fun pp_output_string (state :formatter) s = !(#pp_output_function state) s 0 (String.size s)
and pp_output_newline (state : formatter) = !(#pp_output_newline state) ()
and pp_display_blanks (state : formatter) n = !(#pp_output_spaces state) n
;;

(* To format a break, indenting a new line. *)
fun break_new_line (state : formatter) offset width = (
  pp_output_newline state;
  #pp_is_new_line state := true;
  let val indent = !(#pp_margin state) - width + offset
  (* Don't indent more than pp_max_indent. *)
      val real_indent = Int.min(!(#pp_max_indent state) , indent) in (
  (#pp_current_indent state) := real_indent;
  (#pp_space_left state) := !(#pp_margin state) - !(#pp_current_indent state) ;
  pp_display_blanks state (!(#pp_current_indent state))
  )
  end
);;

(* To force a line break inside a block: no offset is added. *)
fun break_line state width =  break_new_line state 0 width;;

(* To format a break that fits on the current line. *)
fun break_same_line state width =(
  (#pp_space_left state) := !(#pp_space_left state) - width;
  pp_display_blanks state width
);;


(* To indent no more than pp_max_indent, if one tries to open a block
   beyond pp_max_indent, then the block is rejected on the left
   by simulating a break. *)
fun pp_force_break_line state =
  case !(#pp_format_stack state) of
    Format_elem (bl_ty, width) :: _ =>
    if width > !(#pp_space_left state) then
      (case bl_ty of
         Pp_fits => () | Pp_hbox => ()
       | Pp_vbox   => (break_line state width)
	   | Pp_hvbox  => (break_line state width)
	   | Pp_hovbox => (break_line state width)
	   | Pp_box    => (break_line state width)
	  )
    else ()
  | [] => pp_output_newline state
;;

(* To skip a token, if the previous line has been broken. *)
fun pp_skip_token (state : formatter) =
  (* When calling pp_skip_token the queue cannot be empty. *)
  case take_queue (!(#pp_queue state)) of
    { elem_size = ref size, length = len, token = _ } => (
    (#pp_left_total state) := !(#pp_left_total state) - len;
    (#pp_space_left state) := !(#pp_space_left state) + int_of_size size
	)
;;

exception Not_found;;

(**************************************************************

  The main pretty printing functions.

 **************************************************************)

(* To format a token. *)
fun format_pp_token (state : formatter) size = fn

    Pp_text s => (
    (#pp_space_left state) := !(#pp_space_left state) - size;
    pp_output_string state s;
    (#pp_is_new_line state) := false
    )
  | Pp_begin (off, ty) =>(
    let val insertion_point = !(#pp_margin state) - !(#pp_space_left state) in
    if insertion_point > !(#pp_max_indent state) then
      (* can't open a block right there. *)
      (pp_force_break_line state ) else () 
	end;
    let val offset = !(#pp_space_left state) - off 
        val bl_type =
      ( case ty of
        Pp_vbox => Pp_vbox
      | Pp_hbox    => if size > !(#pp_space_left state) then ty else Pp_fits
	  | Pp_hvbox   => if size > !(#pp_space_left state) then ty else Pp_fits
	  | Pp_hovbox  => if size > !(#pp_space_left state) then ty else Pp_fits
	  | Pp_box     => if size > !(#pp_space_left state) then ty else Pp_fits
	  | Pp_fits    => if size > !(#pp_space_left state) then ty else Pp_fits
      ) in
    #pp_format_stack state :=
      Format_elem (bl_type, offset) :: !(#pp_format_stack state) 
    end)
	
  | Pp_end =>
    ( case !(#pp_format_stack state) of
      _ :: ls => (#pp_format_stack state) := ls
    | [] => () (* No more block to close. *)
    )

  | Pp_tbegin (tbox as (Pp_tbox _)) =>
    #pp_tbox_stack state := tbox :: !(#pp_tbox_stack state) 

  | Pp_tend =>
    ( case !(#pp_tbox_stack state) of
      _ :: ls => (#pp_tbox_stack state) := ls
    | [] => () (* No more tabulation block to close. *)
    )

  | Pp_stab =>
    ( case !(#pp_tbox_stack state) of
      Pp_tbox tabs :: _ =>
      let fun add_tab n = fn
          [] => [n]
        | ls as(x :: l) => if n < x then n :: ls else x :: add_tab n l in
      tabs := add_tab (!(#pp_margin state) - !(#pp_space_left state) ) (!tabs)
	  end
    | [] => () (* No opened tabulation block. *)
    )

  | Pp_tbreak (n, off) =>
    let val insertion_point = !(#pp_margin state) - !(#pp_space_left state) in
    ( case !(#pp_tbox_stack state) of
      Pp_tbox tabs :: _ =>
      let fun find n = fn
          x :: l => if x >= n then x else find n l
        | [] => raise Not_found 
          val tab =
        case !tabs of
          x :: _ =>
          (
            (find insertion_point (!tabs)) 
			handle Not_found => x
          )
        | _ => insertion_point 
          val offset = tab - insertion_point in
      if offset >= 0
      then break_same_line state (offset + n)
      else ( break_new_line state (tab + off) (!(#pp_margin state) ))
	  end
    | [] => () (* No opened tabulation block. *)
    )
	end

  | Pp_newline =>
    ( case !(#pp_format_stack state) of
      Format_elem (_, width) :: _ => break_line state width
    | [] =>  pp_output_newline state (* No opened block. *)
    )

  | Pp_if_newline =>
    if (!(#pp_current_indent state)) <> (!(#pp_margin state)) - (!(#pp_space_left state)) 
    then pp_skip_token state else ()

  | Pp_break (n, off) =>
    ( case !(#pp_format_stack state) of
      Format_elem (ty, width) :: _ =>
      ( case ty of
        Pp_hovbox =>
        if size > !(#pp_space_left state) 
        then break_new_line state off width
        else break_same_line state n
      | Pp_box =>
        (* Have the line just been broken here ? *)
        if !(#pp_is_new_line state) then break_same_line state n else
        if size > !(#pp_space_left state) 
         then break_new_line state off width else
        (* break the line here leads to new indentation ? *)
        if !(#pp_current_indent state) > !(#pp_margin state) - width + off
        then break_new_line state off width
        else break_same_line state n
      | Pp_hvbox => break_new_line state off width
      | Pp_fits => break_same_line state n
      | Pp_vbox => break_new_line state off width
      | Pp_hbox => break_same_line state n
      )
    | [] => () (* No opened block. *)
    )

   | Pp_open_tag tag_name =>
     let val marker = !(#pp_mark_open_tag state) tag_name in
     pp_output_string state marker;
     (#pp_mark_stack state) := tag_name :: !(#pp_mark_stack state) 
	 end

   | Pp_close_tag =>
     ( case !(#pp_mark_stack state) of
       tag_name :: tags =>
       let val marker = (!(#pp_mark_close_tag state)) tag_name in (
       pp_output_string state marker;
       (#pp_mark_stack state) := tags
	   )
	   end
     | [] => () (* No more tag to close. *)
     )
;;

(* Print if token size is known or printing is delayed.
   Size is known when not negative.
   Printing is delayed when the text waiting in the queue requires
   more room to format than exists on the current line.

   Note: [advance_loop] must be tail recursive to prevent stack overflows. *)
fun advance_loop (state : formatter) =
  ( 
  case peek_queue (!(#pp_queue state)) of
    {elem_size = ref size, token = tok, length = len} =>
    let val size = int_of_size size in
	(
    if not
         (size < 0 andalso
          (!(#pp_right_total state) - !(#pp_left_total state) < !(#pp_space_left state) ))
    then (
      ignore (take_queue (!(#pp_queue state)) );
      format_pp_token state (if size < 0 then pp_infinity else size) tok;
      (#pp_left_total state) := len + !(#pp_left_total state) ;
      advance_loop state
    ) else ()
	)
	end
	)
;;

fun advance_left state =
  (advance_loop state) handle
   Empty_queue => ()
;;

fun enqueue_advance state tok = (pp_enqueue state tok; advance_left state);;

(* To enqueue a string : try to advance. *)
fun make_queue_elem size tok len =
  { elem_size = ref size, token = tok, length = len };; 

  
fun enqueue_string_as state size s =
  let val len = int_of_size size in
  enqueue_advance state (make_queue_elem size (Pp_text s) len)
  end
;;
  
fun enqueue_string state s =
  let val len = String.size s in
  enqueue_string_as state (size_of_int len) s
  end
;;

(* Routines for scan stack
   determine sizes of blocks. *)

(* The scan_stack is never empty. *)
val scan_stack_bottom =
  let val q_elem = make_queue_elem (size_of_int (~1)) (Pp_text "") 0 in
  [Scan_elem (~1, q_elem)]
  end
;;

(* Set size of blocks on scan stack:
   if ty = true then size of break is set else size of block is set;
   in each case pp_scan_stack is popped. *)
fun clear_scan_stack (state : formatter) = (#pp_scan_stack state) := scan_stack_bottom;;

(* Pattern matching on scan stack is exhaustive,
   since scan_stack is never empty.
   Pattern matching on token in scan stack is also exhaustive,
   since scan_push is used on breaks and opening of boxes. *)

fun set_size (state : formatter) ty =
  case !(#pp_scan_stack state) of
    Scan_elem
      (left_tot,
       (queue_elem as { elem_size = ref size, token = tok, length = _ })) :: t =>
    let val size = int_of_size size in
    (* test if scan stack contains any data that is not obsolete. *)
    if left_tot < !(#pp_left_total state) then clear_scan_stack state else
      ( case tok of
        Pp_break (_, _)  =>
		if ty then
        (
          (#elem_size queue_elem) := size_of_int ( !(#pp_right_total state) + size);
          (#pp_scan_stack state) := t
        ) else ()
	  | Pp_tbreak (_, _) =>
        if ty then
        (
          (#elem_size queue_elem) := size_of_int ( !(#pp_right_total state) + size);
          (#pp_scan_stack state) := t
        ) else ()
      | Pp_begin (_, _) =>
        if not ty then
        (
          (#elem_size queue_elem) := size_of_int ( !(#pp_right_total state) + size);
          (#pp_scan_stack state) := t
        ) else ()
      | Pp_text _ => () | Pp_stab => () | Pp_tbegin _ => () | Pp_tend => () | Pp_end
      => () | Pp_newline => () | Pp_if_newline
      => () | Pp_open_tag _ => () | Pp_close_tag =>
        () (* scan_push is only used for breaks and boxes. *)
      )
	end
  | [] => () (* scan_stack is never empty. *)
;

(* Push a token on scan stack. If b is true set_size is called. *)
fun scan_push (state : formatter) b tok =(
  pp_enqueue state tok;
  if b then set_size state true else ();
  (#pp_scan_stack state) :=
    Scan_elem ( !(#pp_right_total state), tok) :: (!(#pp_scan_stack state))
);;


(* To open a new block :
   the user may set the depth bound pp_max_boxes
   any text nested deeper is printed as the ellipsis string. *)
fun pp_open_box_gen (state : formatter) indent br_ty =(
  (#pp_curr_depth state) := !(#pp_curr_depth state) + 1;
  if !(#pp_curr_depth state) < !(#pp_max_boxes state) then
    let val elem =
      make_queue_elem
        (size_of_int (~ (!(#pp_right_total state)) ))
        (Pp_begin (indent, br_ty))
        0 in
    scan_push state false elem 
	end
  else if !(#pp_curr_depth state) = !(#pp_max_boxes state) 
  then enqueue_string state (!(#pp_ellipsis state)) else ()
);;

(* The box which is always opened. *)
fun pp_open_sys_box state = pp_open_box_gen state 0 Pp_hovbox;;

(* Close a block, setting sizes of its sub blocks. *)
fun pp_close_box state () =
  if !(#pp_curr_depth state) > 1 then
  (
    if !(#pp_curr_depth state) < !(#pp_max_boxes state) then
    (
      pp_enqueue state
        { elem_size = ref (size_of_int 0), token = Pp_end, length = 0 };
      set_size state true; set_size state false
    ) else ();
    (#pp_curr_depth state) := !(#pp_curr_depth state) - 1
  ) else ()
;;

fun pp_set_print_tags (state:formatter) b = #pp_print_tags state := b;;
fun pp_set_mark_tags (state:formatter) b = #pp_mark_tags state := b;;
fun pp_get_print_tags (state:formatter) () = !(#pp_print_tags state);;
fun pp_get_mark_tags (state:formatter) () = !(#pp_mark_tags state);;
fun pp_set_tags (state:formatter) b = (pp_set_print_tags state b; pp_set_mark_tags state b);;

(* Initialize pretty-printer. *)
fun pp_rinit (state: formatter) = (
  pp_clear_queue state;
  clear_scan_stack state;
  (#pp_format_stack state ) := [];
  (#pp_tbox_stack state ) := [];
  (#pp_tag_stack state ) := [];
  (#pp_mark_stack state ) := [];
  (#pp_current_indent state ) := 0;
  (#pp_curr_depth state ) := 0;
  (#pp_space_left state ) := !(#pp_margin state) ;
  pp_open_sys_box state
);;

(* Flushing pretty-printer queue. *)
fun pp_flush_queue (state : formatter) b = (
  while !(#pp_curr_depth state ) > 1 do
    (pp_close_box state ());
  (#pp_right_total state ) := pp_infinity;
  advance_left state;
  if b then pp_output_newline state else ();
  pp_rinit state
) ;;

(**************************************************************

  Procedures to format objects, and use boxes

 **************************************************************)

(* To format a string. *)
fun pp_print_as_size state size s =
  if !(#pp_curr_depth state ) < !(#pp_max_boxes state) 
  then enqueue_string_as state size s else ()
;;

fun pp_print_as state isize s =
  pp_print_as_size state (size_of_int isize) s
;;

fun pp_print_string state s =
  pp_print_as state (String.size s) s
;;

(* To format an integer. *)
fun pp_print_int state i = pp_print_string state (Int.toString i);;

(* Opening boxes. *)
fun pp_open_hbox state () = pp_open_box_gen state 0 Pp_hbox
fun pp_open_box state indent = pp_open_box_gen state indent Pp_box;;
fun pp_open_hvbox state indent = pp_open_box_gen state indent Pp_hvbox;;

(* Print a new line after printing all queued text
   (same for print_flush but without a newline). *)
fun pp_print_newline state () = (
  pp_flush_queue state true; !(#pp_flush_function state ) ()
)
and pp_print_flush state () = (
  pp_flush_queue state false; !(#pp_flush_function state ) ()
);; 

fun pp_print_break state width offset =
  if !(#pp_curr_depth state) < !(#pp_max_boxes state) then
    let val elem =
      make_queue_elem
        (size_of_int (~ (!(#pp_right_total state)) ))
        (Pp_break (width, offset))
        width in
    scan_push state true elem
	end
  else ()
;;

fun pp_print_space state () = pp_print_break state 1 0;;

(**************************************************************

  Procedures to control the pretty-printers

 **************************************************************)

(* Fit max_boxes. *)
fun pp_set_max_boxes (state:formatter) n = if n > 1 then #pp_max_boxes state := n else ();;

(* To set the margin of pretty-printer. *)
fun pp_limit n =
  if n < pp_infinity then n else pred pp_infinity
;;

fun pp_set_min_space_left state n =
  if n >= 1 then
    let val n = pp_limit n in (
    #pp_min_space_left state := n;
    #pp_max_indent state := !(#pp_margin state) - !(#pp_min_space_left state);
    pp_rinit state
	) end
  else ()
;;

(* Initially, we have :
  pp_max_indent = pp_margin - pp_min_space_left, and
  pp_space_left = pp_margin. *)
fun pp_set_max_indent (state:formatter) n =
  pp_set_min_space_left state (!(#pp_margin state) - n)
;;

fun pp_set_margin state n =
  if n >= 1 then
    let val n = pp_limit n 
	in
	  (
        (#pp_margin state) := n;
        let val new_max_indent =
          (* Try to maintain max_indent to its actual value. *)
          if !(#pp_max_indent state) <= !(#pp_margin state) then 
  		    !(#pp_max_indent state)
  		  else
          (* If possible maintain pp_min_space_left to its actual value,
             if this leads to a too small max_indent, take half of the
             new margin, if it is greater than 1. *)
            max (max (!(#pp_margin state) - !(#pp_min_space_left state))
                    (!(#pp_margin state) div 2)) 1 
    	in
          (* Rebuild invariants. *)
          pp_set_max_indent state new_max_indent
        end
	  )
	end
  else ()
;;

fun default_pp_mark_open_tag s = "<" ^ s ^ ">";;
fun default_pp_mark_close_tag s = "</" ^ s ^ ">";;

fun default_pp_print_open_tag _ = ();;
fun default_pp_print_close_tag x = default_pp_print_open_tag x;;

fun pp_make_formatter f g h i =
  (* The initial state of the formatter contains a dummy box. *)
  let val pp_q = make_queue () 
      val sys_tok =
    make_queue_elem (size_of_int (~1)) (Pp_begin (0, Pp_hovbox)) 0 in (
  add_queue sys_tok pp_q;
  let val sys_scan_stack =
      (Scan_elem (1, sys_tok)) :: scan_stack_bottom in
  ({
   pp_scan_stack = ref  sys_scan_stack,
   pp_format_stack = ref  [] ,
   pp_tbox_stack = ref [] ,
   pp_tag_stack = ref [],
   pp_mark_stack = ref [],
   pp_margin = ref 78,
   pp_min_space_left = ref 10,
   pp_max_indent = ref (78 - 10), 
   pp_space_left = ref 78,
   pp_current_indent = ref 0,
   pp_is_new_line = ref true,
   pp_left_total = ref 1,
   pp_right_total = ref 1,
   pp_curr_depth = ref 1,
   pp_max_boxes = ref max_int,
   pp_ellipsis = ref ".",
   pp_output_function = ref f,
   pp_flush_function = ref g,
   pp_output_newline = ref h,
   pp_output_spaces = ref i,
   pp_print_tags = ref false,
   pp_mark_tags = ref false,
   pp_mark_open_tag = ref default_pp_mark_open_tag,
   pp_mark_close_tag = ref default_pp_mark_close_tag, 
   pp_print_open_tag = ref default_pp_print_open_tag,
   pp_print_close_tag = ref default_pp_print_close_tag,
   pp_queue = ref pp_q
  } : formatter) end ) end
;;

(* Default function to output spaces. *)
val blank_line = string_make 80 #" ";;

fun display_blanks (state : formatter) n =
  if n > 0 then
  if n <= 80 then !(#pp_output_function state ) blank_line 0 n else
  (
    !(#pp_output_function state ) blank_line 0 80;
    display_blanks state (n - 80)
  ) else ()
;;

(* Default function to output new lines. *)
fun display_newline (state : formatter) () = !(#pp_output_function state ) "\n" 0  1;;

(* Make a formatter with default functions to output spaces and new lines. *)
fun make_formatter output flush =
  let val ppf = pp_make_formatter output flush ignore ignore in (
  (#pp_output_newline ppf ) := display_newline ppf;
  (#pp_output_spaces ppf ) := display_blanks ppf;
  ppf
  ) end
;;

fun formatter_of_out_channel oc =
  make_formatter (output oc) (fn () => TextIO.flushOut oc)
;;

(* Predefined formatters. *)
(* val str_formatter = formatter_of_buffer stdbuf;; *)
val std_formatter = formatter_of_out_channel TextIO.stdOut;;
val err_formatter = formatter_of_out_channel TextIO.stdErr;;

(**************************************************************

  Basic functions on the standard formatter

 **************************************************************)

 val open_hbox = pp_open_hbox std_formatter;;
 val open_hvbox = pp_open_hvbox std_formatter;;
 val open_box = pp_open_box std_formatter;;
 val close_box = pp_close_box std_formatter;;
 val print_break = pp_print_break std_formatter;;
 val print_string = pp_print_string std_formatter;;
 val print_space = pp_print_space std_formatter;;
 val print_flush = pp_print_flush std_formatter;;
 val print_newline = pp_print_newline std_formatter;;
 val print_int = pp_print_int std_formatter;;
 
 val set_margin = pp_set_margin std_formatter;;
 val set_max_indent = pp_set_max_indent std_formatter;;
 val set_max_boxes = pp_set_max_boxes std_formatter;;
 val set_mark_tags =
    pp_set_mark_tags std_formatter;;
