load "Timer";;
load "Time";;
val timer = Timer.startRealTimer ();; 
use "init.sml";;
print("Total time used: " ^ (Real.toString (Time.toReal (Timer.checkRealTimer timer))) ^ " seconds\n");;

