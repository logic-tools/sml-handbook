SML version of code for John Harrison's "Handbook of Practical Logic and Automated Reasoning" (Chapter 6 on Interactive Theorem Proving only).
===

John Harrison's "Handbook of Practical Logic and Automated Reasoning" (Cambridge University Press 2009) teaches both propositional logic and first-order logic as well as how computer programs can be used to reason using these logics. Furthermore, the book presents the OCaml code of such programs.

### Contents ###
The SML folder contains a partial translation of the OCaml code. In addition it contains Init.thy, which runs the program in Isabelle. Furthermore it contains full_test.sml and verbose_functions.sml which are used for testing. Lastly it contains timing.sml which is used for timing.
The OCaml folder contains the source code of the book downloaded from John Harrison's website. The files fol.ml, folderived.ml, lcffol.ml, meson.ml, prop.ml, resolution.ml and tableaux.ml are the fixed versions mentioned under Errata on the webpage. Furthermore the OCaml folder contains full_test.ml and verbose_functions.ml which are used for testing. Lastly, for reference, it contains a copy of the format.ml library from the OCaml distribution.
The auxi folder contains an auxiliary program which is used for printing the test results.
Finally the tests folder contains test results.

### Tests ###
The OCaml version contains many examples that are run when executing the code. These examples are also present in this SML version. Furthermore, the examples have been collected in the file full_test.sml. This file uses verbose_functions.sml which contains versions of the functions that are modified to print their results after execution. For OCaml the corresponding examples are collected in full_test.ml which similarly uses verbose_functions.ml.
Each test case in full_test.sml and full_test.ml is printed as follows: First as a line ":::" is printed, then the result from a function is printed, and lastly a line with ";;;" is printed. The program cleaner.sml can then be used to collect these results by only printing the lines that are encapsuled in pair of ":::" and ";;;".
This has been done for both full_test.sml and full_test.ml and both gave the same result:

$ cd SML
$ echo -e "use \"init.sml\";;\n use \"full_test.sml\";;\n quit ();;" | mosml > ../tests/executionSML.txt 2>&1
$ cd ../OCaml
$ echo -e "#use \"init.ml\";;\n #use \"full_test.ml\";;\n#quit;;" | ocaml > ../tests/executionOCaml.txt 2>&1
$ cd ../tests
$ cat executionSML.txt   | mosml ../auxi/cleaner.sml > resultSML.txt
$ cat executionOCaml.txt | mosml ../auxi/cleaner.sml > resultOCaml.txt
$ diff resultSML.txt resultOCaml.txt
$ tail -n 6 resultSML.txt
|- (p ==> q) \/ (q ==> p)
|- p /\ q <=> (p <=> q) <=> p \/ q
|- ((p <=> q) <=> r) <=> p <=> q <=> r
> val it = () : unit
[closing file "../auxi/cleaner.sml"]
- 
$ 

The latest tests were done in Mac OS X Version 10.11.3.

### LICENSE ###

Unless otherwise stated:

Copyright (c) 2015, Anders Schlichtkrull, Jørgen Villadsen
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* The name of Anders Schlichtkrull or Jørgen Villadsen may not be 
used to endorse or promote products derived from this software without 
specific prior written permission of each person.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.
