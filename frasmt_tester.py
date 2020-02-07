from __future__ import absolute_import

import sys
import logging
import time
import frasmt_solver as solver
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition

# End of imports

logging.disable(logging.FATAL)

# Path and naming scheme for output files
base_output_path = '/tmp'
base_output_file = 'slv2'

for i in range(15, 200, 2):
    if i == 18 or i == 20:
        continue

    sys.stdout.write("Instance {}\n".format(i))
    file = "/home/aschidler/Downloads/htd-exact-public/htd-exact_{:03d}.hgr".format(i)

    arcs = None
    ord = None
    last_val = None
    edges = None
    bags = None
    res = None

    for htd in [False, True]:
        # Create encoding of the instance
        before_tm = time.time()

        if htd is None and res is not None:
            res = solver.solve(base_output_path, base_output_file, file, htd=True, arcs=arcs, sb=False,
                               fix_val=last_val, timeout=900)
        elif htd is not None:
            # This uses the previous result as a lower bound for the htd encoding, good to test portfolio approach
            # bad to compare
            lb = None if res is None else res.size

            res = solver.solve(base_output_path, base_output_file, file, htd=htd, sb=False, timeout=900, lb=None, heuristic_repair=False)
            if htd is None:
                htd = True

        if res is None:
            sys.stdout.write("Failed!\tTime:{}\n".format(time.time() - before_tm))
        else:
            # Display the HTD
            td = res.decomposition
            num_edges = len(td.T.edges)
            arcs = res.arcs
            ord = res.ordering
            last_val = res.size
            edges = [(i, j) for i, j in td.tree.edges]
            bags = td.bags

            valid = td.validate(td.hypergraph)
            valid_ghtd = GeneralizedHypertreeDecomposition.validate(td, td.hypergraph)
            valid_sc = td.inverse_edge_function_holds()

            sys.stdout.write("{}\tResult: {}\tValid:  {}\tSP: {}\tGHTD: {}\tTime: {}\n".format(
                htd,
                res.size,
                valid,
                valid_sc,
                valid_ghtd,
                time.time() - before_tm
            ))

    sys.stdout.write("\n")
