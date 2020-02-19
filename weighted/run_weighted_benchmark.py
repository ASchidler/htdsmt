import sys
import time
import logging

import smt_solver as solver
from lib.htd_validate.htd_validate.decompositions import GeneralizedHypertreeDecomposition

instance = sys.argv[1]
weighted_instances = 2
tmp_dir = sys.argv[2]
logging.disable(logging.FATAL)
fl = 'ghtw_solver2'


def run_portfolio(c_instance, weighted):
    lb = None
    res = solver.solve(tmp_dir, fl, c_instance, htd=False, sb=False, heuristic_repair=True, clique_mode=0,
                       weighted=weighted)
    td = res.decomposition if res is not None else None
    if td is not None and GeneralizedHypertreeDecomposition.validate(td, td.hypergraph):
        lb = res.size

    # Use stratified encoding
    if res is not None and not td.validate(td.hypergraph):
        td = res.decomposition
        arcs = res.arcs
        result = res.size

        # Compute stratified solution
        res = solver.solve(tmp_dir, fl, c_instance, htd=True, fix_val=result,
                           arcs=arcs, heuristic_repair=False, weighted=weighted)
        td = res.decomposition if res is not None else None

    # Use HTD encoding
    if td is None or not td.validate(td.hypergraph):
        res = solver.solve(tmp_dir, fl, c_instance, sb=False,
                           heuristic_repair=False, lb=lb, weighted=weighted)
        td = res.decomposition

    if td is not None and td.validate(td.hypergraph):
        return res


for i in range(1, weighted_instances+1):
    instance = sys.argv[1] + f".w{i}"

    tm_start = time.time()
    res = run_portfolio(instance, False)

    weight = 0
    for f in res.decomposition.hyperedge_function.values():
        weight = max(weight, sum(res.decomposition.hypergraph.weights()[k] for k, v in f.items() if v > 0))
    print(f"GHTW{i}: {weight} - width: {res.size} in {time.time() - tm_start}")

    tm_start = time.time()
    res = run_portfolio(instance, True)

    ghtw = 0
    for f in res.decomposition.hyperedge_function.values():
        ghtw = max(ghtw, sum(1 for v in f.values() if v > 0))

    print(f"WGHTW{i}: {res.size} - width: {ghtw} in {time.time() - tm_start}")
