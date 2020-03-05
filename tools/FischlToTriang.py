import os
import sys
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
import networkx as nx
from itertools import combinations

for r, d, f in os.walk(sys.argv[1]):
    for fl in f:
        file = os.path.join(r, fl)
        hg = Hypergraph.from_file(file, fischl_format=True)

        outp = os.path.join(sys.argv[2], fl)
        with open(outp, "w") as of:
            for e in hg.edges():
                ce = []
                for n in hg.get_edge(e):
                    ce.append(str(n))

                of.write(f"{' '.join(ce)}\n")
