from __future__ import absolute_import

import sys
import inspect
import frasmt_solver
import os
import subprocess
import logging
import time
import threading
import networkx as nx


from lib.htd_validate.htd_validate.utils import Hypergraph
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition

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
slv = './optimathsat' if not is_z3 else 'z3'

for i in range(17, 23, 2):
    if i == 18 or i == 19:
        continue

    sys.stdout.write("Instance {}\n".format(i))
    file = "/home/aschidler/Downloads/htd-exact-public/htd-exact_{:03d}.hgr".format(i)
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
        # Create temporary files
        inpf = open(inp_file, "w+")
        modelf = open(model_file, "w+")
        errorf = open(err_file, "w+")

        # Create encoding of the instance
        before_tm = time.time()
        enc = frasmt_solver.FraSmtSolver(hypergraph, stream=inpf, checker_epsilon=None)

        if htd is None:
            enc.solve(htd=True, force_lex=False, edges=edges, fix_val=last_val, sb=False)
        else:
            enc.solve(htd=htd, sb=htd)

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
        try:
            res = enc.decode(outp, is_z3, htd=htd, repair=(htd is False))
        except ValueError as ee:
            # If htd is none, this simply means, that the result is unsat, i.e. cannot be repaired
            sys.stdout.write("{}\tResult: Failed\t Time:{}\n".format(
                htd,
                time.time() - before_tm
            ))
            continue

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

    sys.stdout.write("\n")
