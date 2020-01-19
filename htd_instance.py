from networkx import Graph
from itertools import combinations


class HtdInstance:
    def __init__(self, hypergraph):
        self.hg = hypergraph
        self.pg = Graph()
        for e in self.hg.edges():
            for u, v in combinations(self.hg.get_edge(e), 2):
                self.pg.add_edge(u, v)