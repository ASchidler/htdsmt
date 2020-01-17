from c_htw.c_result import CDecompositionResult


class CHtwEncoding:
    def __init__(self, tw_encoding, stream, c_edges):
        self.encoding = tw_encoding
        self.stream = stream
        self.c_edges = c_edges

    def solve(self, cfirst=True, use_c=True, clique=None, twins=None, htd=True, sb=True, weighted=False):
        self.encoding.encode(clique=clique, twins=twins, htd=htd, sb=sb, weighted=weighted, enforce_lex=False)
        varname = "c"

        # We know c to be smaller than m, help the solver
        if use_c:
            self.stream.write(f"(declare-const c Int)\n")
            self.stream.write(f"(assert (>= c 1))\n")
            self.stream.write(f"(assert (<= c m))\n")

            # Add cardinality constraints
            if len(self.c_edges) > 0:
                n = self.encoding.hypergraph.number_of_nodes()
                for j in range(1, n + 1):
                    weights = []
                    for e in self.c_edges:
                        assert (e > 0)
                        weights.append("weight_{j}_e{e}".format(j=j, e=e))

                    weights = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]

                    self.stream.write(f"(assert (<= {weights} c))\n")

        if use_c:
            if cfirst:
                self.stream.write(f"(minimize (+ m (* c {len(self.encoding.hypergraph.edges())})))\n")
            else:
                self.stream.write(f"(minimize (+ c (* m {len(self.encoding.hypergraph.edges())})))\n")
        else:
            self.stream.write(f"(minimize m)\n")

        self.stream.write("(check-sat)\n(get-model)\n")

    def find_lb(self, hypergraph):
        # Find hyperedges whose vertices are unique to c-edges
        pass

    def decode(self, output, htd=False):
        res = self.encoding.decode(output, False, htd=htd, repair=False, weighted=False)
        c = max(len([x for x in self.c_edges if cv[x] > 0]) for cv in res.weights.values())

        return CDecompositionResult(c, res)


