theory Init
imports Main
begin

SML_import {* val load = (fn _ => ()) *}
SML_import {* val use = (fn _ => ()) *} 

SML_file "init.sml"
SML_file "format.sml"
SML_file "initialization.sml"
SML_file "lib.sml"
SML_file "intro.sml"
SML_file "formulas.sml"
SML_file "prop.sml"
SML_file "fol.sml"
SML_file "skolem.sml"
SML_file "unif.sml"
SML_file "tableaux.sml"
SML_file "resolution.sml"
SML_file "equal.sml"
SML_file "order.sml"
SML_file "eqelim.sml"
SML_file "lcf.sml"
SML_file "lcfprop.sml"
SML_file "folderived.sml"
SML_file "lcffol.sml"
SML_file "tactics.sml"

SML_export {* 
  val res =
    let val p = Atom(R("p",[])) 
        val q = Atom(R("q",[]))
    in 
      lcftaut (Or(Imp(p,q),Imp(q,p))) 
    end 
*}

ML {* res *}

end
