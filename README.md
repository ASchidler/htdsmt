# HtdSMT - An SMT based solver for hypertree decompositions

This is a solver for computing optimal (generalized) hypertree decompositions. It is an adapted version of the FraSMT solver (https://github.com/daajoe/frasmt).

This version contains the code and experiments used in the paper "Threshold Treewidth and Hypertree Width" (https://www.ijcai.org/proceedings/2020/263), the respective code can be found in the subfolder "c_htw".

The solver is written in Python 2 and requires the optimathsat solver (http://optimathsat.disi.unitn.it/).

To start it either call "python frasmt_runner.py <Filename>" or pass the instance via STDIN to "python frasmt_runner.py" 

