from __future__ import absolute_import

import re
from itertools import combinations

from networkx.algorithms.dag import descendants

from lib.htd_validate.htd_validate.decompositions import HypertreeDecomposition
from lib.htd_validate.htd_validate.utils import HypergraphPrimalView

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
        for i in range(1, n + 1):
            # TODO: so far more variables
            for j in range(i + 1, n + 1):
                # for j in range(i + 1, n + 1):
                # (declare-const ord_ij Bool)
                self.ord[i][j] = self.add_var(name='ord_%s_%s' % (i, j))
                self.stream.write("(declare-const ord_{i}_{j} Bool)\n".format(i=i, j=j))

        # arcs
        self.arc = [[None for j in range(n + 1)] for i in range(n + 1)]
        # self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # declare arc_ij variables
                self.arc[i][j] = self.add_var(name='arc_%s_%s' % (i, j))
                self.stream.write("(declare-const arc_{i}_{j} Bool)\n".format(i=i, j=j))

        # weights
        self.weight = [[None for ej in range(m + 1)]
                       for j in range(n + 1)]

        for j in range(1, n + 1):
            for ej in range(1, m + 1):
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

        for j in range(1, n + 1):
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
        tord = lambda p, q: 'ord_{p}_{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}_{p})'.format(p=p, q=q)

        # Some improvements
        for i in range(1, n + 1):
            for j in range(i+1, n + 1):
                # Arcs cannot go in both directions
                self.add_clause([-self.arc[j][i], -self.arc[i][j]])
                # Enforce arc direction from smaller to bigger ordered vertex
                self.add_clause([-self.ord[i][j], -self.arc[j][i]])
                self.add_clause([self.ord[i][j], -self.arc[i][j]])

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write("(assert (=> {ordvar} (not arc_{j}_{i})))\n".format(i=i, j=j, ordvar=tord(i, j)))

                for l in range(1, n + 1):
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

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for l in range(j + 1, n + 1):
                    if i == l:
                        continue

                    # AS CLAUSE
                    # These to clauses are entailed by the improvement clauses and the next clause
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    # self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redundant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        # forbid self loops
        for i in range(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            # self.stream.write("(assert (not arc_{i}_{i}))\n".format(i=i))
            self.add_clause([-self.arc[i][i]])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )
        # TODO: double-check the iterator over i

        for i in range(1, n + 1):
            for j in range(1, n + 1):
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

    def encode_htd(self, n, enforce_lex=True):

        def tord(ix, jx):
            return 'ord_{}_{}'.format(ix, jx) if ix < jx else '(not ord_{}_{})'.format(jx, ix)

        vvars = []
        m = self.hypergraph.number_of_edges()

        # # Whenever a tree node covers an edge, it covers all of the edge's vertices
        for i in range(1, n+1):
            for j in range(1, n + 1):
                self.stream.write("(declare-const covers_{}_{} Bool)\n".format(i, j))

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                vvars = []
                for e in self.hypergraph.incident_edges(j):
                    vvars.append("(> weight_{i}_e{e} 0)".format(i=i, e=e))
                    self.stream.write("(assert (=> (= weight_{i}_e{e} 1) covers_{i}_{j}))\n".format(i=i, j=j, e=e))
                self.stream.write("(assert (or (not covers_{i}_{j}) {vvars}))\n".format(vvars=" ".join(vvars), i=i, j=j))

        # Establish root
        for i in range(1, n + 1):
            self.stream.write("(declare-const is_root_{} Bool)\n".format(i))
            vvars.append("is_root_{}".format(i))

            # Smaller nodes cannot be root
            for j in range(1, n + 1):
                if i == j:
                    continue

                ordvar = tord(i, j)
                self.stream.write("(assert (=> {ordvar} (not is_root_{i})))\n".format(ordvar=ordvar, i=i))

        # There has to be a root
        self.stream.write("(assert (or {vvars}))\n".format(vvars=" ".join(vvars)))

        # Establish predecessor
        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue

                self.stream.write("(declare-const is_pred_{}_{} Bool)\n".format(i, j))

        for i in range(1, n + 1):
            vvars = []
            for j in range(1, n + 1):
                if i == j:
                    continue
                vvars.append("is_pred_{i}_{j}".format(i=i, j=j))

        #         # No node shared, or is smaller (in terms of the orderign) -> no predecessor
                ordvar = tord(i, j)
                self.stream.write("(assert (=> (not arc_{i}_{j}) (not is_pred_{i}_{j})))\n".format(i=i, j=j))
        #         self.stream.write("(assert (=> {ordvar} (not is_pred_{j}_{i})))\n".format(ordvar=ordvar, i=i, j=j))
        #
        #         # If there is a smaller node with a shared variable in between -> no predecessor
                for k in range(1, n+1):
                    if k == i or k == j:
                        continue

                    ordvar2 = tord(j, k)
                    #
                    # self.stream.write("(assert (or (not arc_{i}_{j}) (not {v1}) (not {v2}) (not is_pred_{i}_{k})))\n"
                    #                   .format(v2=ordvar2, v1=ordvar, i=i, j=j, k=k,
                    #                           ))
                    self.stream.write("(assert (or (not arc_{i}_{j}) (not {ord}) (not is_pred_{i}_{k})))\n"
                                                  .format(ord=tord(j, k), i=i, j=j, k=k,
                                                          ))

            # A node is either the root, or it has a predecessor
            self.stream.write("(assert (or is_root_{i} {vvars}))\n".format(vvars=" ".join(vvars), i=i))

        # Establish descendents
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                self.stream.write("(declare-const is_desc_{}_{} Bool)\n".format(i, j))

        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                ordvar = tord(i, j)
                self.stream.write("(assert (=> is_pred_{i}_{j} is_desc_{i}_{j}))\n".format(i=i, j=j))
                self.stream.write("(assert (=> {ordvar} (not is_desc_{j}_{i})))\n".format(i=i, j=j, ordvar=ordvar))

                for k in range(1, n+1):
                    if k == i or k == j:
                        continue

                    # Transitivity of real descendency
                    self.stream.write("(assert (or (not is_desc_{i}_{j}) (not is_desc_{j}_{k}) is_desc_{i}_{k}))\n"
                                       .format(i=i, j=j, k=k))

                    # If the parent is not a descendant of another node, so isn't the successor
                    self.stream.write("(assert (or (not is_pred_{i}_{j}) is_desc_{j}_{k} (not is_desc_{i}_{k})))\n"
                                      .format(i=i, j=j, k=k))

        # Add equivalence relation
        for i in range(1, n+1):
            for j in range(i+1, n+1):
                self.stream.write("(declare-const eql_{}_{} Bool)\n".format(i, j))

        for i in range(1, n + 1):
            for j in range(i + 1, n + 1):

                # This seems to slow down the solving...
                # if enforce_lex:
                #     # Enforce lexicographic ordering and arcs within the group
                #     self.stream.write("(assert (or (not eql_{i}_{j}) {ord}))\n"
                #                       .format(i=i, j=j, ord=tord(i, j)))
                #     self.stream.write("(assert (or (not eql_{i}_{j}) arc_{i}_{j}))\n"
                #                       .format(i=i, j=j, ord=tord(i, j)))
                # else:
                # Enforce that nodes are connected within group
                self.stream.write("(assert (or (not eql_{i}_{j}) (not {ord}) arc_{i}_{j}))\n"
                                  .format(i=i, j=j, ord=tord(i, j)))
                self.stream.write("(assert (or (not eql_{i}_{j}) {ord} arc_{j}_{i}))\n"
                                  .format(i=i, j=j, ord=tord(i, j)))

                for k in range(j + 1, n + 1):
                    # Transitivity of eql
                    self.stream.write("(assert (or (not eql_{i}_{j}) (not eql_{j}_{k}) eql_{i}_{k}))\n"
                                      .format(i=i, j=j, k=k))
                    self.stream.write("(assert (or (not eql_{i}_{k}) (not eql_{j}_{k}) eql_{i}_{j}))\n"
                                      .format(i=i, j=j, k=k))
                    self.stream.write("(assert (or (not eql_{i}_{j}) (not eql_{i}_{k}) eql_{j}_{k}))\n"
                                      .format(i=i, j=j, k=k))

                for k in range(1, n+1):
                    if k == i or k == j:
                        continue

                    # Enforce same outgoing arcs
                    self.stream.write("(assert (or (not eql_{i}_{j}) (not arc_{i}_{k}) (not {ord}) arc_{j}_{k}))\n"
                                      .format(i=i, j=j, k=k, ord=tord(j, k)))

                    self.stream.write("(assert (or (not eql_{i}_{j}) (not arc_{j}_{k}) (not {ord}) arc_{i}_{k}))\n"
                                      .format(i=i, j=j, k=k, ord=tord(i, k)))

                    if k != j and k > i:
                        # Groups must be continuous in the ordering. Do not enforce this without enforce lex,
                        # as this may be incompatible with the establishes GHTD
                        if enforce_lex:
                            self.stream.write("(assert (or (not {ord1}) (not {ord2}) (not eql_{i}_{k}) eql_{i}_{j}))\n"
                                              .format(i=i, j=j, k=k, ord1=tord(i, j), ord2=tord(j, k)))

                for e in range(1, m + 1):
                    self.stream.write("(assert (or (not eql_{i}_{j}) (not (= weight_{i}_e{e} 1)) (= weight_{j}_e{e} 1)))\n"
                                      .format(i=i, j=j, e=e))
                    self.stream.write("(assert (or (not eql_{i}_{j}) (not (= weight_{j}_e{e} 1)) (= weight_{i}_e{e} 1)))\n"
                        .format(i=i, j=j, e=e))

        # Add bag finding
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                self.stream.write("(declare-const is_bag_{}_{} Bool)\n".format(i, j))

        for i in range(1, n + 1):
            self.stream.write("(assert is_bag_{i}_{i})\n".format(i=i))

            for j in range(1, n + 1):
                if i == j:
                    continue

                ordvar = tord(i, j)
                self.stream.write("(assert (=> (and arc_{i}_{j} {ordvar}) is_bag_{i}_{j}))\n".format(i=i, j=j, ordvar=ordvar))

                if j > i:
                    # These four clauses seem redundant but are not
                    # Bag membership requires an arc
                    self.stream.write(
                        "(assert (=> (and (not arc_{i}_{j}) (not eql_{i}_{j})) (not is_bag_{i}_{j})))\n".format(i=i, j=j, ordvar=ordvar))
                    self.stream.write(
                        "(assert (=> (and (not arc_{j}_{i}) (not eql_{i}_{j})) (not is_bag_{j}_{i})))\n".format(i=i,
                                                                                                                j=j,
                                                                                                                ordvar=ordvar))
                    # Lower ordered nodes are not allowed, if not in the same equivalence class
                    self.stream.write(
                        "(assert (=> (and (not {ordvar}) (not eql_{i}_{j})) (not is_bag_{i}_{j})))\n".format(i=i, j=j, ordvar=ordvar))
                    self.stream.write(
                        "(assert (=> (and {ordvar} (not eql_{i}_{j})) (not is_bag_{j}_{i})))\n".format(i=i, j=j, ordvar=ordvar))

            for j in range(i+1, n+1):
                self.stream.write(
                    "(assert (=> eql_{i}_{j} is_bag_{i}_{j}))\n".format(i=i, j=j))

                self.stream.write(
                    "(assert (=> eql_{i}_{j} is_bag_{j}_{i}))\n".format(i=i, j=j))

        # Finally verify the constraint
        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue

                for k in range(1, n + 1):
                    ordvar1 = tord(i, k)
                    ordvar2 = tord(j, k)
                    self.stream.write(
                        "(assert (or (not is_desc_{i}_{j}) (not is_bag_{i}_{k}) (not covers_{j}_{k}) is_bag_{j}_{k}))\n"
                        .format(i=i, j=j, k=k, v1=ordvar1, v2=ordvar2))

    def break_order_symmetry(self):
        n = self.hypergraph.number_of_nodes()

        def tord(ix, jx):
            return 'ord_{}_{}'.format(ix, jx) if ix < jx else '(not ord_{}_{})'.format(jx, ix)

        for i in range(1, n+1):
            for j in range(i+1, n+1):
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    self.stream.write("(declare-const block_{}_{}_{} Bool)\n".format(i, j, k))

        for i in range(1, n+1):
            vvars = []
            for j in range(i+1, n+1):
                for k in range(1, n + 1):
                    if i == k or j == k:
                        continue

                    # self.stream.write(
                    #     "(assert (or {ord1} (not {ord2}) (not arc_{k}_{i}) block_{i}_{j}_{k}))\n"
                    #         .format(i=i, j=j, k=k, ord1=tord(i, j), ord2=tord(j, k)))
                    # self.stream.write(
                    #     "(assert (or (not block_{i}_{j}_{k}) (not {ord1})))\n"
                    #     .format(i=i, j=j, k=k, ord1=tord(i, j), ord2=tord(j, k)))
                    self.stream.write(
                        "(assert (or (not {ord}) (not arc_{k}_{i}) block_{i}_{j}_{k}))\n"
                            .format(i=i, j=j, k=k, ord=tord(j, k)))
                    self.stream.write(
                        "(assert (or (not block_{i}_{j}_{k}) {ord}))\n"
                            .format(i=i, j=j, k=k, ord=tord(j, k)))
                    self.stream.write(
                        "(assert (or (not block_{i}_{j}_{k}) arc_{k}_{i}))\n"
                            .format(i=i, j=j, k=k))

                    vvars.append("block_{i}_{j}_{k}".format(i=i, j=j, k=k))

                self.stream.write("(assert (or ord_{i}_{j} arc_{j}_{i} {vvars}))\n".format(vvars=" ".join(vvars), i=i, j=j))

    def encode(self, clique=None, twins=None, htd=True, arcs=None, order=None, enforce_lex=True, edges=None, bags=None, sb=True):
        n = self.hypergraph.number_of_nodes()

        self.break_clique(clique=clique)
        self.elimination_ordering(n)
        self.cover(n)
        self.encode_twins(twin_iter=twins, clique=clique)
        if sb:
            self.break_order_symmetry()

        if htd:
            self.encode_htd(n, enforce_lex)

        if arcs:
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i == j:
                        continue

                    if arcs[i][j]:
                        self.stream.write("(assert (or arc_{i}_{j} arc_{j}_{i}))\n".format(i=i, j=j))

        if order:
            for i in order:
                for j in range(i+1, n+1):
                    if order.index(i) < order.index(j):
                        self.stream.write("(assert ord_{i}_{j})\n".format(i=i, j=j))
                    else:
                        self.stream.write("(assert (not ord_{i}_{j}))\n".format(i=i, j=j))

        if edges:
            for i, j in edges:
                self.stream.write("(assert (or is_pred_{i}_{j} is_pred_{j}_{i}))\n".format(i=i, j=j))

        if bags:
            for i, b in bags.iteritems():
                for j in b:
                    self.stream.write("(assert is_bag_{i}_{j})\n".format(i=i, j=j))

    def solve(self, clique=None, twins=None, optimize=True, htd=True, limit=None, arcs=None, order=None, force_lex=True,
              fix_val=None, edges=None, bags=None, sb=True):
        var = self.add_var("m")
        m = self._vartab[var]
        self.stream.write("(declare-const m Int)\n")
        self.stream.write("(assert (>= m 1))\n")

        if fix_val:
            self.stream.write("(assert (= m {}))\n".format(fix_val))
        elif limit:
            self.stream.write("(assert (>= m {}))\n".format(limit))

        self.prepare_vars()

        self.encode(clique=clique, twins=twins, htd=htd, arcs=arcs, order=order, enforce_lex=force_lex, edges=edges, bags=bags, sb=sb)

        # assert(False)
        self.fractional_counters(m=m)
        # self.add_all_at_most(m)

        # #THERE IS A PROBLEM WITH MINIMIZATION APPARENTLY
        # # #WIE WILL STEFAN PROGRESSION ERKLAEREN???
        if optimize:
            self.stream.write("(minimize m)\n")
        self.stream.write("(check-sat)\n(get-model)\n")

    def decode(self, output, is_z3, htd=False, repair=True):
        ret = {"objective": "nan", "decomposition": None, "arcs": None, "ord": None, "weights": None}

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
            arcs = self._get_arcs(model)
            edges = self._get_edges(model) if htd else None
            bags = self._get_bags(model) if htd else None
            #edges = None
            #arcs = None
            #edges = None

            htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                        weights=weights,
                                                        checker_epsilon=self.__checker_epsilon, edges=edges, bags=bags, htd=htd, repair=repair)

            # Debug, verify if the descendent relation is correct
            if htd:
                desc = self._get_desc(model)
                for n in htdd.tree.nodes:
                    actual = set(descendants(htdd.tree, n))
                    if len(desc[n]) != len(actual) or len(desc[n]-actual) > 0:
                        print("Failed on node {}, mismatch".format(n, desc[n] - actual))
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

        ret.update({"objective": htdd.width(), "decomposition": htdd, "arcs": arcs, "ord": ordering, "weights": weights})
        # if not htd.validate(self.hypergraph):
        #     raise RuntimeError("Found a GHTD that is not a HTD")

        return ret

    def _get_ordering(self, model):
        ordering = []
        for i in range(1, self.hypergraph.number_of_nodes() + 1):
            pos = 0
            for j in ordering:
                # We know j is smaller due to range processing
                if not model["ord_{}_{}".format(j, i)]:
                    break
                # Move current element one position forward
                pos += 1
            ordering.insert(pos, i)

        return ordering

    def _get_weights(self, model, ordering):
        ret = {}
        n = self.hypergraph.number_of_nodes()

        for i in range(1, n + 1):
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

    def _get_edges(self, model):
        n = self.hypergraph.number_of_nodes()
        edges = []
        for i in range(1, n+1):
            for j in range(1, n+1):
                if i == j:
                    continue

                if model["is_pred_{}_{}".format(i, j)]:
                    edges.append((j, i))

        return edges

    def _get_bags(self, model):
        n = self.hypergraph.number_of_nodes()
        ret = {}

        for i in range(1, n+1):
            ret[i] = {}
            #ret[i][i] = True
            for j in range(1, n+1):
                #if i != j:
                ret[i][j] = model["is_bag_{}_{}".format(i, j)]

        return ret

    def _get_arcs(self, model):
        n = self.hypergraph.number_of_nodes()
        ret = {}

        for i in range(1, n+1):
            ret[i] = {}
            #ret[i][i] = True
            for j in range(1, n+1):
                if i != j:
                    ret[i][j] = model["arc_{}_{}".format(i, j)]

        return ret

    def _get_desc(self, model):
        n = self.hypergraph.number_of_nodes()
        desc = {}
        for i in range(1, n+1):
            val = set()
            for j in range(1, n+1):
                if i == j:
                    continue

                if model["is_desc_{}_{}".format(j, i)]:
                    val.add(j)
            desc[i] = val

        return desc

    def _get_eq(self, model):
        n = self.hypergraph.number_of_nodes()
        desc = {i: set() for i in range(1, n+1)}
        for i in range(1, n+1):
            for j in range(i + 1, n+1):
                if model["eql_{}_{}".format(i, j)]:
                    desc[i].add(j)
                    desc[j].add(i)

        return desc
