from __future__ import absolute_import

import re
from itertools import combinations
from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from decomposition_result import DecompositionResult
from lib.htd_validate.htd_validate.utils import HypergraphPrimalView
from networkx import DiGraph


class FraSmtSolver:
    def __init__(self, hypergraph, stream, wprecision=20, timeout=0, checker_epsilon=None):
        self.__checker_epsilon = checker_epsilon
        self.hypergraph = hypergraph
        self.num_vars = 1
        self.num_cls = 0
        self.timeout = timeout

        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []
        self.wprecision = wprecision
        self.stream.write('(set-option :print-success false)\n(set-option :produce-models true)\n')

    def prepare_vars(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        for i in range(1, n + 1):
            self.stream.write("(declare-const root_{i} Bool)\n".format(i=i))

            for j in range(1, n + 1):
                self.stream.write("(declare-const desc_{i}_{j} Bool)\n".format(i=i, j=j))
                self.stream.write("(declare-const bag_{i}_{j} Bool)\n".format(i=i, j=j))

            for ej in range(1, m + 1):
                self.stream.write("(declare-const weight_{i}_e{ej} Int)\n".format(i=i, ej=ej))
                self.stream.write("(assert (<= weight_{i}_e{ej} 1))\n".format(i=i, ej=ej))
                self.stream.write("(assert (>= weight_{i}_e{ej} 0))\n".format(i=i, ej=ej))

    # prepare variables
    def counters(self):
        n = self.hypergraph.number_of_nodes()

        for j in range(1, n + 1):
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            weights = f"(+ {' '.join(weights)})" if len(weights) > 1 else weights[0]

            self.stream.write("(assert (<= {weights} m))\n".format(weights=weights))

            # set optimization variable or value for SAT check

    def structure(self, n):
        # There has to be one root
        root_vars = []
        for i in range(1, n+1):
            root_vars.append("root_{i}".format(i=i))
            for j in range(i+1, n+1):
                self.stream.write("(assert (or (not root_{i}) (not root_{j})))\n".format(i=i, j=j))

        self.stream.write("(assert (or {}))\n".format(" ".join(root_vars)))

        # Descendancy, transitivity and one-directedness
        for i in range(1, n+1):
            self.stream.write("(assert (not desc_{i}_{i}))\n".format(i=i))

            for j in range(1, n+1):
                if i == j:
                    continue

                self.stream.write("(assert (or (not root_{i}) desc_{j}_{i}))\n".format(i=i, j=j))
                self.stream.write("(assert (or (not desc_{i}_{j}) (not desc_{j}_{i})))\n".format(i=i, j=j))
                for k in range(1, n+1):
                    if i == k or j == k:
                        continue
                    # Transitivity
                    self.stream.write("(assert (or (not desc_{i}_{j}) (not desc_{j}_{k}) desc_{i}_{k}))\n".
                                      format(i=i, j=j, k=k))
                    # Enforces only one parent
                    self.stream.write("(assert (or (not desc_{i}_{j}) (not desc_{i}_{k}) desc_{j}_{k} desc_{k}_{j}))\n".
                                      format(i=i, j=j, k=k))

    def bags(self, n):
        for i in range(1, n+1):
            self.stream.write("(assert bag_{i}_{i})\n".format(i=i))

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i != j:
                    # AS CLAUSE
                    self.stream.write("(assert (or desc_{i}_{j} desc_{j}_{i}))\n".format(i=i, j=j))
                    self.stream.write("(assert (or (not desc_{i}_{j}) bag_{i}_{j}))\n".format(i=i, j=j))
                    self.stream.write("(assert (or (not desc_{j}_{i}) bag_{j}_{i}))\n".format(i=i, j=j))

        # Connectedness
        # Connectedness of v in the subtree rooted at v
        clause = ["(not desc_{i}_{j})", "(not desc_{j}_{k})", "(not bag_{i}_{k})", "bag_{j}_{k}"]
        # Connectedness of v in case v occurs above v
        clause2 = ["(not desc_{i}_{j})", "(not desc_{j}_{k})", "(not bag_{k}_{i})", "bag_{j}_{i}"]

        clause_str = "(assert (or {vars}))\n".format(vars=" ".join(clause))
        clause_str2 = "(assert (or {vars}))\n".format(vars=" ".join(clause2))
        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue
                self.stream.write(
                    "(assert (or desc_{i}_{j} desc_{j}_{i} (not bag_{j}_{i})))\n".format(i=i, j=j))
                for k in range(1, n+1):
                    if i == k or j == k:
                        continue
                    self.stream.write(clause_str.format(i=i, j=j, k=k))
                    self.stream.write(clause_str2.format(i=i, j=j, k=k))

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                summed = f">= (+ {' '.join(weights)}) 1" if len(weights) > 1 else ">= "+ weights[0] +" 1"

                self.stream.write(
                    "(assert (=> bag_{i}_{j} ({weights})))\n".format(i=i, j=j, weights=summed))

    def special_condition(self, n):
        # Find out which nodes cover which vertices
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                self.stream.write("(declare-const covers_{i}_{j} Bool)\n".format(i=i, j=j))

            for e in self.hypergraph.edges():
                # PRIMAL GRAPH CONSTRUCTION
                for j in self.hypergraph.get_edge(e):
                    self.stream.write("(assert (or (= weight_{i}_e{e} 0) covers_{i}_{j}))\n".format(i=i, j=j, e=e))

        for i in range(1, n+1):
            for j in range(1, n+1):
                for k in range(1, n+1):
                    if i == k:
                        continue

                    clauses = "bag_{i}_{j} (not covers_{i}_{j}) (not desc_{k}_{i}) (not bag_{k}_{j})"\
                        .format(i=i, j=j, k=k)
                    self.stream.write("(assert (or {clauses}))\n".format(clauses=clauses))

    def solve(self, optimize=True, htd=True, lb=None, ub=None, arcs=None, order=None, force_lex=True,
              fix_val=None, edges=None, bags=None, sb=True, weighted=False):
        n = self.hypergraph.number_of_nodes()

        self.stream.write("(declare-const m Int)\n")
        self.stream.write("(assert (>= m 1))\n")

        if fix_val:
            self.stream.write("(assert (= m {}))\n".format(fix_val))
        else:
            if ub:
                self.stream.write("(assert (<= m {}))\n".format(lb))
            if lb:
                self.stream.write("(assert (>= m {}))\n".format(lb))

        self.prepare_vars()
        self.structure(n)
        self.cover(n)
        self.bags(n)
        self.counters()

        if htd:
            self.special_condition(n)

        if optimize:
            self.stream.write("(minimize m)\n")
        self.stream.write("(check-sat)\n(get-model)\n")

    def decode(self, output, is_z3, htd=False, repair=True, weighted=None):
        model = {}

        if not is_z3:
            lines = re.findall('\(([^ ]+) ([a-zA-Z0-9\( \/\)]*)\)', output)

            for nm, val in lines:
                # Last entry sometimes has the closing ) in the line
                val = val.replace(")", "").strip()

                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                elif "/" in val:
                    str = val.replace("(", "").replace(")", "").replace("/", "").strip().split(" ")
                    model[nm] = int(str[0]) * 1.0 / int(str[1])
                else:
                    model[nm] = int(val)

        try:
            bags = self._get_bags(model)
            desc = self._get_desc(model)
            weights = self._get_weights(model)

            tree = DiGraph()
            while len(desc) > 0:
                ck = set()
                # Find leafs
                for k, v in list(desc.items()):
                    if len(v) == 0:
                        ck.add(k)
                        desc.pop(k)

                # Find parent
                for k in ck:
                    # Find potential parents
                    cand = set()
                    for o, v in desc.items():
                        if k in v:
                            cand.add(o)
                            v.remove(k)

                    # Find the parent, the node that has no other candidates below
                    for o in cand:
                        if len(desc[o] & cand) == 0:
                            tree.add_edge(o, k)
                            #break

            htdd = HypertreeDecomposition(hypergraph=self.hypergraph, tree=tree, bags=bags, hyperedge_function=weights)

            # Debug, verify if the descendent relation is correct
            # if htd:
            #     desc = self._get_desc(model)
            #     for n in htdd.tree.nodes:
            #         actual = set(descendants(htdd.tree, n))
            #         if len(desc[n]) != len(actual) or len(desc[n]-actual) > 0:
            #             print("Failed on node {}, mismatch".format(n, desc[n] - actual))
        #
        # if htd:
        #     eql = self._get_eq(model)
        #
        #     for i, j in eql.iteritems():
        #         print "{}: {}".format(i, j)


        # if htd:
        #     ts = self._get_t(model)
        #     for n in list(htdd.tree.nodes):
        #         if not ts[n]:
        #             #print n
        #             htdd.tree.remove_node(n)

        except KeyError:
            raise ValueError("Could not parse output. In case of mode 2 may indicate unsat, otherwise check error log.")

        # if not htd.validate(self.hypergraph):
        #     raise RuntimeError("Found a GHTD that is not a HTD")

        return DecompositionResult(htdd.width(), htdd, None, None, weights)

    def _get_desc(self, model):
        n = self.hypergraph.number_of_nodes()
        desc = {i: set() for i in range(1, n+1)}

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # We know j is smaller due to range processing
                if model["desc_{j}_{i}".format(i=i, j=j)]:
                    desc[i].add(j)

        return desc

    def _get_weights(self, model):
        ret = {}
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n + 1):
            # print 'bag %i'
            ret[i] = {}
            for e in self.hypergraph.edges():
                assert (e > 0)
                ret[i][e] = model["weight_{}_e{}".format(i, e)]

        return ret

    def _get_bags(self, model):
        n = self.hypergraph.number_of_nodes()
        ret = {}

        for i in range(1, n+1):
            ret[i] = set()

            for j in range(1, n+1):
                if model["bag_{i}_{j}".format(i=i, j=j)]:
                    ret[i].add(j)

        return ret