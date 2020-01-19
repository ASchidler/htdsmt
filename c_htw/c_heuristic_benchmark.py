import sys
import os
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
from c_htw.c_encoding import CHtwEncoding
from frasmt_encoding import FraSmtSolver
from shutil import which
import subprocess
import random
import bounds.upper_bounds as ub
import htd_instance

input_file = sys.argv[1]
result_path = sys.argv[2]

ratios = [0.05, 0.1, 0.2, 0.3]
timeout = 1800

hypergraph = Hypergraph.from_file(input_file, fischl_format=True)

# Random sort edges, use fixed seed for reproducibility
random.seed(len(hypergraph.edges()) + len(hypergraph.nodes()))
he = list(hypergraph.edges())
for i in range(0, len(he)-1):
    nxt = random.randint(i, len(he)-1)
    he[i], he[nxt] = he[nxt], he[i]

instance = htd_instance.HtdInstance(hypergraph)
print(ub.greedy(instance, htd=False, bb=False)[0])
print(ub.greedy(instance, htd=False, bb=True)[0])
