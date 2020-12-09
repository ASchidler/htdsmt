import sys
import os
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph

pth = sys.argv[1]

for r, d, f in os.walk(pth):
    for c_file in f:
        if c_file.endswith(".hg"):
            hg = Hypergraph.from_file(os.path.join(r, c_file), fischl_format=True)
            print(f"{c_file};{hg.number_of_nodes()};{hg.number_of_edges()}")
