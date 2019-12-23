import sys
import time

import weighted.weight_upper_bound as wub
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph

instance = sys.argv[1]
weighted_instances = 2
tmp_dir = sys.argv[2]

fl = 'ghtw_solver2'

for i in range(1, weighted_instances+1):
    instance = sys.argv[1] + f".w{i}"


    hypergraph_in = Hypergraph.from_file(instance, fischl_format=False)
    hypergraph2 = Hypergraph.from_file(instance, fischl_format=True, weighted=True)

    if hypergraph_in is None or (hypergraph2 is not None and len(hypergraph2.edges()) > len(hypergraph_in.edges())):
        hypergraph_in = hypergraph2

    tm_start = time.time()
    weight1 = wub.greedy(hypergraph_in, bb=False)
    tm1 = time.time()
    weight2 = wub.greedy(hypergraph_in, bb=True)
    tm2 = time.time()

    print(f"Heuristisc WGHTW{i}: {weight1} in {tm1 - tm_start}")
    print(f"Heuristisc BBWGHTW{i}: {weight1} in {tm2 - tm1}")