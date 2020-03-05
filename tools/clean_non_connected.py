import os
import sys
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph
import networkx as nx
from itertools import combinations

cnt = 0
for r, d, f in os.walk(sys.argv[1]):
    for fl in f:
        file = os.path.join(r, fl)
        hg = Hypergraph.from_file(file, fischl_format=True)
        pg = nx.Graph()
        for e in hg.edges():
            for u, v in combinations(hg.get_edge(e), 2):
                pg.add_edge(u, v)

        if len(pg.nodes) < 2 or not nx.is_connected(pg):
            cmp = nx.connected_components(pg)
            cnt += 1
            os.remove(file)

print(f"Found {cnt} files")
