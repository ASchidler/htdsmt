from __future__ import absolute_import

import sys
import inspect
import frasmt_solver
import os
import subprocess
import logging
import time
import threading

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from htd_validate import Hypergraph
from htd_validate.decompositions import GeneralizedHypertreeDecomposition

# End of imports
# Use z3 or mathsat?
is_z3 = False
# Filenames and paths to use
inp_file = '/tmp/slv.encode'
model_file = '/tmp/slv.model'
err_file = '/tmp/slv.err'

# Disable logging, otherwise PACE runs fail... Exceptions will still terminate the run
logging.disable(logging.FATAL)

# Encode solver as string, uncomment before submitting!
# if is_z3:
#     solver_decoder.encode_z3()
# else:
#     solver_decoder.encode_os()

# Load solver and check permissions
slv = 'optimathsat' if not is_z3 else 'z3'

for i in xrange(31, 200, 2):
    if i == 17 or i == 19:
        continue

    sys.stdout.write("Instance {}\n".format(i))
    file = "htd-exact-public/htd-exact_{:03d}.hgr".format(i)
    hypergraph = Hypergraph.from_file(file, fischl_format=False)

    # Launch SMT solver
    src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
    src_path = os.path.realpath(os.path.join(src_path, '..'))

    arcs = None
    ord = None
    last_val = None
    edges = None
    bags = None

    for htd in [False, None, True]:
        try:
            # Create temporary files
            inpf = open(inp_file, "w+")
            modelf = open(model_file, "w+")
            errorf = open(err_file, "w+")

            # Create encoding of the instance
            before_tm = time.time()
            enc = frasmt_solver.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)

            if htd is None:
                enc.solve(htd=True, force_lex=False, edges=edges, fix_val=last_val)
            else:
                enc.solve(htd=htd)

            if htd is None:
                htd = True

            # Solve using the SMT solver
            inpf.seek(0)
            if is_z3:
                p1 = subprocess.Popen([slv, '-smt2', '-in'], stdin=inpf, stdout=modelf, stderr=errorf)
            else:
                p1 = subprocess.Popen(slv, stdin=inpf, stdout=modelf, stderr=errorf, shell=True)

            p1.wait()

            # Retrieve the result
            modelf.seek(0)
            errorf.seek(0)
            outp = modelf.read()
            errp = errorf.read()

            inpf.close()
            modelf.close()
            errorf.close()

            solved = (len(errp) == 0)

            # Load the resulting model
            res = enc.decode(outp, is_z3, htd=htd)

            # Display the HTD
            td = res['decomposition']
            num_edges = len(td.T.edges)
            arcs = res['arcs']
            ord = res['ord']
            last_val = res['objective']
            edges = [(i, j) for i, j in td.tree.edges]
            bags = td.bags

            valid = td.validate(td.hypergraph)
            valid_ghtd = GeneralizedHypertreeDecomposition.validate(td, td.hypergraph)
            valid_sc = td.inverse_edge_function_holds()

            sys.stdout.write("{}\tResult: {}\tValid:  {}\tSP: {}\tGHTD: {}\tTime: {}\n".format(
                htd,
                res['objective'] if solved else -1,
                valid,
                valid_sc,
                valid_ghtd,
                time.time() - before_tm
            ))

            # for i,j in td.bags.iteritems():
            #     print "{}: {}".format(i, j)
            # for i, j in td.tree.edges:
            #     print "{} {}".format(i, j)

        except (RuntimeError, KeyError):
            sys.stderr.write("An error occurred:\n")

    sys.stdout.write("\n")
