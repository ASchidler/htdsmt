import htd_instance


class CInstance(htd_instance.HtdInstance):
    def __init__(self, hypergraph, c_edges):
        super().__init__(hypergraph)
        self.c_edges = c_edges
