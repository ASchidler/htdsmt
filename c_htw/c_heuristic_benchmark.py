import random
import sys

import bounds.upper_bounds as ub
import c_htw.c_upper_bounds as cub
from c_htw.c_instance import CInstance
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
import os

input_file = sys.argv[1]
result_path = sys.argv[2]

ratios = [0.05, 0.1, 0.2, 0.3]

hypergraph = Hypergraph.from_file(input_file, fischl_format=True)
_, instance_name = os.path.split(input_file)

# Random sort edges, use fixed seed for reproducibility
random.seed(len(hypergraph.edges()) + len(hypergraph.nodes()))
he = list(hypergraph.edges())


def calc_c(cover, inst):
    return max(sum(v for e, v in ent.items() if v > 0 and e in inst.c_edges) for ent in cover.values())


for i in range(0, len(he)-1):
    nxt = random.randint(i, len(he)-1)
    he[i], he[nxt] = he[nxt], he[i]

for ratio in ratios:
    result_file = instance_name
    result_file += ("%.2f" % ratio)[1:]
    result_file += ".heuristic"
    result_file = os.path.join(result_path, result_file)

    colored = {he[x] for x in range(0, int(len(he) * ratio + 1))}
    results = {}
    instance = CInstance(hypergraph, colored)

    oblivious_g = ub.greedy(instance, htd=False, bb=False)
    results['oblivious_g'] = (oblivious_g[0],  calc_c(oblivious_g[1][2], instance))
    oblivious_b = ub.greedy(instance, htd=False, bb=True)
    results['oblivious_b'] = (oblivious_b[0], calc_c(oblivious_b[1][2], instance))

    cfirst_g = cub.greedy(instance, bb=False, cfirst=True)
    results['cfirst_g'] = (cfirst_g[0], cfirst_g[1])
    cfirst_b = cub.greedy(instance, bb=True, cfirst=True)
    results['cfirst_b'] = (cfirst_b[0], cfirst_b[1])

    clast_g = cub.greedy(instance, bb=False, cfirst=False)
    results['clast_g'] = (clast_g[0], clast_g[1])
    clast_b = cub.greedy(instance, bb=True, cfirst=False)
    results['clast_b'] = (clast_b[0], clast_b[1])

    with open(result_file, "w+") as outp:
        names = list(results.keys())
        names.sort()
        # minimum found width and minimum found c
        outp.write(f"{min(v[0] for v in results.values())};{min(v[1] for v in results.values())}")
        for n in names:
            outp.write(f";{results[n][0]};{results[n][1]}")
        outp.write(os.linesep)

