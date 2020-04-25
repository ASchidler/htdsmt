import sys
import time

import weighted.weight_upper_bound as wub
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph

instance = sys.argv[1]
weighted_instances = 2
tmp_dir = sys.argv[2]

fl = 'ghtw_solver2'

for bb, i in ((x, y) for x in [False, True] for y in range(1, weighted_instances + 1)):
    instance = sys.argv[1] + f".w{i}"

    tm_start = time.time()
    hypergraph_in = Hypergraph.from_file(instance, fischl_format=False)
    hypergraph2 = Hypergraph.from_file(instance, fischl_format=True, weighted=True)

    if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
        hypergraph_in = hypergraph2

    weight1 = wub.greedy(hypergraph_in, bb=bb)

    print(f"Heuristisc WGHTW{i}: BB: {bb} {weight1} in {time.time() - tm_start}")
    sys.stdout.flush()
