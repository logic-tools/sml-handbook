load "TextIO";;
open TextIO;;

fun hasNext input =
  case lookahead input of
    NONE => false
  | SOME _ => true;;
  
fun substr (s,i,j) =
  SOME (substring (s,i,j))
  handle Subscript => NONE;;

val write = ref false;;

fun readFile () =
  case inputLine stdIn of
    SOME line =>(
      if substr(line, 0, 3) = SOME ":::" then
        write := true
      else if substr(line, 0, 3) = SOME ";;;" then
        write := false
      else if !write then
        print line
      else ();
	  readFile()
    )
  | NONE => ()
;;
readFile();;
