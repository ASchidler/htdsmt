# HtdSAMT - An SAT/SMT based solver for Hypertree Decompositions

This is a decomposer for hypergraphs. It finds optimal (generalized) hypertree decompositions. It is based on FraSMT
(https://github.com/daajoe/frasmt) and extends the original idea to HTDs.

The code is written in Python3 and it can solve the instance either by using SMT or SAT.

In order to use SMT, call smt_runner.py and supply the instance as the main argument. 
The solver expects optimathsat (http://optimathsat.disi.unitn.it/) to be either in the path 
or in the folder.

In order to use SAT, call sat_runner.py and supply the instance as the main argument. 
The solver expects glucose (https://www.labri.fr/perso/lsimon/glucose/) to be either in
the path or in the folder. By adapting the subprocess call in sat_runner.py it is easy to
use any other SAT solver (tested with lingeling, minisat)

Both, the SAT and the SMT, runners accept the flag "-g" to compute a generalized
generalized hypertree decomposition, instead of a hypertree decomposition.
 

