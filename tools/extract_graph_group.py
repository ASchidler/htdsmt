import sys
import os
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph

pth = sys.argv[1]

for r, d, f in os.walk(pth):
    for c_file in f:
        if c_file.endswith(".hg"):
            print(f"{c_file};{os.path.split(r)[-1]}")
