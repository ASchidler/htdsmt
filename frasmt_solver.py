from __future__ import absolute_import

from decimal import Decimal
from itertools import combinations
import re
import os
import sys
import inspect


src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))
from htd_validate.decompositions import FractionalHypertreeDecomposition, HypertreeDecomposition


class FraSmtSolver:
    def __init__(self, hypergraph, stream, wprecision=20, timeout=0, checker_epsilon=None):
        self.__checker_epsilon = checker_epsilon
        self.hypergraph = hypergraph
        self.num_vars = 1
        self.num_cls = 0
        self.timeout = timeout
        self.ord = None
        self.arc = None
        self.weight = None

        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []
        self.wprecision = wprecision
        self.stream.write('(set-option :print-success false)\n(set-option :produce-models true)\n')

    def prepare_vars(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # self.ord = np.zeros((n + 1, n + 1), dtype=int)
        self.ord = [[None for j in range(n + 1)] for i in range(n + 1)]
        # ordering
        for i in xrange(1, n + 1):
            # TODO: so far more variables
            for j in xrange(i + 1, n + 1):
                # for j in xrange(i + 1, n + 1):
                # (declare-const ord_ij Bool)
                self.ord[i][j] = self.add_var(name='ord_%s_%s' % (i, j))
                self.stream.write("(declare-const ord_{i}_{j} Bool)\n".format(i=i, j=j))

        # arcs
        self.arc = [[None for j in range(n + 1)] for i in range(n + 1)]
        # self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                # declare arc_ij variables
                self.arc[i][j] = self.add_var(name='arc_%s_%s' % (i, j))
                self.stream.write("(declare-const arc_{i}_{j} Bool)\n".format(i=i, j=j))

        # weights
        self.weight = [[None for ej in xrange(m + 1)]
                       for j in xrange(n + 1)]

        for j in xrange(1, n + 1):
            for ej in xrange(1, m + 1):
                # (declare-const weight_j_e Real)
                self.weight[j][ej] = self.add_var(name='weight_%s_e%s' % (j, ej))
                self.stream.write("(declare-const weight_{i}_e{ej} Int)\n".format(i=j, ej=ej))

                self.stream.write("(assert (<= weight_{i}_e{ej} 1))\n".format(i=j, ej=ej))
                self.stream.write("(assert (>= weight_{i}_e{ej} 0))\n".format(i=j, ej=ej))

    def add_cards(self, C):
        self.cards.append(C)

    # z3.Real
    def add_var(self, name):
        vid = self.num_vars

        self._vartab[vid] = name
        self.num_vars += 1
        # exit(1)
        return vid

    def literal_str(self, x):
        if x < 0:
            ret = '(not %s)' % self._vartab[abs(x)]
        else:
            ret = '%s' % self._vartab.get(x)
        return ret

    def add_clause(self, C):
        # C = map(neg, C)
        # self.stream.write("%s 0\n" %" ".join(map(str,C)))
        self.stream.write("(assert (or %s))\n" % (' '.join([self.literal_str(x) for x in C])))
        self.num_cls += 1

    # prepare variables
    def fractional_counters(self, m=None):
        n = self.hypergraph.number_of_nodes()

        for j in xrange(1, n + 1):
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            # set optimization variable or value for SAT check
            if len(weights) > 1:
                self.stream.write(
                    "(assert ( <= (+ {weights}) {m}))\n".format(weights=" ".join(weights), m=m))
            elif len(weights) == 1:
                self.stream.write("(assert (<= {} {}))\n".format(weights[0], m))

    def elimination_ordering(self, n):
        tord = lambda p, q: 'ord_{p}{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}{p})'.format(p=p, q=q)

        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(1, n + 1):
                    if i == l or j == l:
                        continue
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)

        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self.add_clause([self.ord[i][j], self.arc[j][i]])
                    self.add_clause([-self.ord[i][j], self.arc[i][j]])

        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(j + 1, n + 1):
                    if i == l:
                        continue

                    # AS CLAUSE
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redunant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        # forbid self loops
        for i in xrange(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            # self.stream.write("(assert (not arc_{i}_{i}))\n".format(i=i))
            self.add_clause([-self.arc[i][i]])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )
        # TODO: double-check the iterator over i

        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(j):
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                if len(weights) > 1:
                    self.stream.write(
                        "(assert (=> arc_{i}_{j} (>= (+ {weights}) 1)))\n".format(i=i, j=j, weights=" ".join(weights)))
                else:
                    self.stream.write(
                        "(assert (=> arc_{i}_{j} (>= {weights} 1)))\n".format(i=i, j=j, weights=weights[0]))

                # arc_ij then i most be covered by some edge (because i will end up in one bag)
                weights = []
                for e in self.hypergraph.incident_edges(i):
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                if len(weights) > 1:
                    self.stream.write(
                        "(assert (>= (+ {weights}) 1))\n".format(weights=" ".join(weights)))
                elif len(weights) == 1:
                    self.stream.write("(assert (>= {} 1))\n".format(weights[0]))

    def break_clique(self, clique):
        if clique:
            # Vertices not in the clique are ordered before the clique
            for i in self.hypergraph.nodes():
                if i in clique:
                    continue
                for j in clique:
                    if i < j:
                        self.add_clause([self.ord[i][j]])
                    else:
                        self.add_clause([-self.ord[j][i]])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i != j:
                        if i < j:
                            self.add_clause([self.ord[i][j]])
                        # else:
                        #     self.add_clause([-self.ord[j][i]])

    # twins is a list of list of vertices that are twins
    def encode_twins(self, twin_iter, clique):
        if not clique:
            clique = []
        if twin_iter:
            # vertices of a twin class are order lexicographically
            for twins in twin_iter:
                if len(twins) <= 1:
                    continue
                for i in twins:
                    if i in clique:
                        continue
                    for j in twins:
                        if i != j:
                            if j in clique:
                                continue
                            if i < j:
                                self.add_clause([self.ord[i][j]])

    def encode(self, clique=None, twins=None):
        n = self.hypergraph.number_of_nodes()

        self.elimination_ordering(n)
        self.cover(n)
        self.break_clique(clique=clique)
        self.encode_twins(twin_iter=twins, clique=clique)

    def solve(self, clique=None, twins=None):
        var = self.add_var("m")
        m = self._vartab[var]
        self.stream.write("(declare-const m Int)\n")
        self.stream.write("(assert (>= m 1))\n")

        self.prepare_vars()

        self.encode(clique=clique, twins=twins)

        # assert(False)
        self.fractional_counters(m=m)
        # self.add_all_at_most(m)

        # #THERE IS A PROBLEM WITH MINIMIZATION APPARENTLY
        # # #WIE WILL STEFAN PROGRESSION ERKLAEREN???
        self.stream.write("(minimize m)\n")
        self.stream.write("(check-sat)\n(get-model)\n")

    def decode(self, output, is_z3):
        ret = {"objective": "nan", "decomposition": None}

        model = {}

        if not is_z3:
            lines = re.findall('\(([^ ]*) ([a-zA-Z0-9]*)\)', output)

            for nm, val in lines:
                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                else:
                    model[nm] = int(val)
        else:
            lines = re.findall('\(define\-fun ([^ ]*) \(\) [a-zA-Z]*\s*([a-zA-Z0-9]*)\)', output)

            for nm, val in lines:
                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                else:
                    model[nm] = int(val)

        try:
            ordering = self._get_ordering(model)
            weights = self._get_weights(model, ordering)
            htd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                                  weights=weights,
                                                                  checker_epsilon=self.__checker_epsilon)

        except KeyError as ee:
            sys.stdout.write("Error parsing output\n")
            sys.stdout.write(output)
            sys.stdout.write("\n")
            raise ee

        ret.update({"objective": htd.width(), "decomposition": htd})
#        if not htd.validate(self.hypergraph):
 #           raise RuntimeError("Found a GHTD that is not a HTD")

        return ret

    def _get_ordering(self, model):
        def cmp(i, j):
            if i < j:
                return -1 if model["ord_{}_{}".format(i, j)] else 1
            else:
                return 1 if model["ord_{}_{}".format(j, i)] else -1

        ordering = range(1, self.hypergraph.number_of_nodes() + 1)
        return sorted(ordering, cmp=cmp)

    def _get_weights(self, model, ordering):
        ret = {}
        n = self.hypergraph.number_of_nodes()

        for i in xrange(1, n + 1):
            # print 'bag %i'
            ret[i] = {}
            for e in self.hypergraph.edges():
                assert (e > 0)
                ret[i][e] = model["weight_{}_e{}".format(i, e)]

        last_vertex = ordering[-1]
        incident_edges = self.hypergraph.incident_edges(last_vertex).keys()
        if len(incident_edges) == 0:
            raise TypeError("Fractional Hypertree Decompositions for graphs with isolated vertices.")

        return ret