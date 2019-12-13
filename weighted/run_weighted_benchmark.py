import sys
import time

import frasmt_solver as solver

instance = sys.argv[1]
weighted_instances = 2
tmp_dir = sys.argv[2]

fl = 'ghtw_solver2'

for i in range(1, weighted_instances+1):
    instance = sys.argv[1] + f".w{i}"

    tm_start = time.time()
    res = solver.solve(tmp_dir, fl, instance, htd=False, force_lex=False,
                       sb=False, heuristic_repair=False, clique_mode=1,
                       weighted=False, timeout=900)
    weight = 0
    for f in res.decomposition.hyperedge_function.values():
        weight = max(weight, sum(res.decomposition.hypergraph.weights()[k] for k, v in f.items() if v > 0))
    print(f"GHTW{i}: {weight} - width: {res.size} in {time.time() - tm_start}")

    tm_start = time.time()
    res = solver.solve(tmp_dir, fl, instance, htd=False, force_lex=False,
                       sb=False, heuristic_repair=False, clique_mode=1,
                       weighted=True, timeout=900)

    ghtw = 0
    for f in res.decomposition.hyperedge_function.values():
        ghtw = max(ghtw, sum(1 for v in f.values() if v > 0))

    print(f"WGHTW{i}: {res.size} - width: {ghtw} in {time.time() - tm_start}")
