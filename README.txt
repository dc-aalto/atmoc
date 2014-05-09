Aalto Timed Model Checker -- ATMOC
(c) 2011-2012 Roland Kindermann
roland.kindermann@aalto.fi
http://users.ics.aalto.fi/kindermann



ATMOC allows for the verification of timed systems with timed automata-like
semantics using a timed version of the IC3 algorithm (the default method),
k-Induction (using --ind) and bounded model checking (using -b <k>). For a
description of the timed IC3 algorithm refer to

Roland Kindermann, Tommi Junttila and Ilkka Niemelä. SMT-based Induction Methods
for Timed Systems. FORMATS 2012, Springer 2012.

and for details on the used bounded model checking variant to

Roland Kindermann, Tommi A. Junttila, Ilkka Niemelä. Modeling for Symbolic
Analysis of Safety Instrumented Systems with Clocks. ACSD 2011, pages 185-194,
IEEE 2011.

For more information on the useage of ATMOC execute "python atmoc.py -h".

ATMOC uses  Python Lex-Yacc library PLY (http://www.dabeaz.com/ply/) for
parsing. PLY is developed by David M. Beazley and published under the
BSD-license (cf. PLY-README.txt). Note that PLY generates files needed for
parsing the first time ATMOC is executed, which may result in a higher execution
time than usual.


INSTALLATION

ATMOC is implemented in Python 2. Version 2.5 or later is required.
Compatibility with Python 3.X has not been tested but is somewhat unlikely.

ATMOC uses the SMT-solver Yices. Before ATMOC can be used, Yices needs to be
added. For compilation, the files "libyices.so" from Yices' "lib" directiory
and "yices_c.h" from the "include" directory have to be copied into the ATMOC
directory. Note that the file "libyices.so" is only contained in the
"Yices with GMP dynamically linked" download on the Yices website. At the time
this document was written, this version could be reached via "Download Yices 1"
->"Other distributions can be downloaded here"->"Yices with GMP dynamically
linked". ATMOC was tested with yices version 1.0.31 (and some earlier versions).
Note that Yices itself may need the  GNU Multiprecision library (GMP) to be
installed.

To compile the python wrapper for Yices, execute "make" in the after ATMOC
directory after adding "libyices.so" and "yices_c.h".

IMPORTANT: In order to find the yices wrapper module, LD_LIBRARY_PATH needs to
contain "." on unix systems.



INPUT FORMAT

The input format is based on the input format of the model checker NuSMV
(http://nusmv.fbk.eu/). Essentially, a subset of the NuSMV syntax is extended
by clock variables. A clock variable can be added using
	<var-name> : clock(<reset-condition>);
to the variable section. Such clock variables can the be compared to integer
constants using "<", "<=", "=", ">=" and ">".

For examples of models refer to the "models" directory.

For the precise semantics, refer to the description of symbolic timed transition
systems in
Roland Kindermann, Tommi A. Junttila, Ilkka Niemelä. Modeling for Symbolic
Analysis of Safety Instrumented Systems with Clocks. ACSD 2011, pages 185-194,
IEEE 2011.
The initial constraint of a system is specified using the "INIT" keyword, the
invariant using "INVAR" and the (discrete-step) transition relation using
"TRANS".

