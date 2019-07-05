import logging
from cStringIO import StringIO

from htd_validate.decompositions import GeneralizedHypertreeDecomposition
from htd_validate.utils import Hypergraph, HypergraphPrimalView
from networkx.algorithms.traversal.depth_first_search import dfs_tree
from networkx import DiGraph
from networkx.algorithms.dag import ancestors, descendants
from networkx.algorithms import shortest_path
from networkx.algorithms.lowest_common_ancestors import lowest_common_ancestor
import sys


class HypertreeDecomposition(GeneralizedHypertreeDecomposition):
    _problem_string = 'htd'

    @staticmethod
    def decomposition_type():
        pass

    @staticmethod
    def graph_type():
        return Hypergraph.__name__

    def __init__(self, hypergraph=None, tree=None, bags=None, hyperedge_function=None, epsilon=None,  plot_if_td_invalid=None):
        if epsilon is not None:
            raise TypeError("Tree Decompositions provide exact results. No epsilon expected.")
        super(HypertreeDecomposition, self).__init__(hypergraph=hypergraph, tree=tree, bags=bags,
                                                     hyperedge_function=hyperedge_function)

    def __len__(self):
        return len(self.bags)

    @classmethod
    def from_ordering(cls, hypergraph, ordering=None, weights=None, checker_epsilon=None, edges=None, bags=None, htd=False):

        pgraph_view = HypergraphPrimalView(hypergraph=hypergraph)
        g = cls._from_ordering(hypergraph=pgraph_view, plot_if_td_invalid=False, ordering=ordering, weights=weights,
                                  checker_epsilon=checker_epsilon
                               #,edges=edges
                               )

        g.hypergraph = hypergraph

        if bags:
            g.bags = {}
            for i in ordering:
                g.bags[i] = set()
                for j in ordering:
                    if bags[i][j]:
                        g.bags[i].add(j)

        if edges:
            g.tree = DiGraph()

            for i, j in edges:
                g.tree.add_edge(i, j)

        if htd:
            return g

        # For the HTD the root is important. Try to find a root
        ug = g.tree.to_undirected()

        #
        # We have a ghtd, now try to repair it to a htd
        # Try each node as a root. Next try to repair the bags. This may not yield a valid decomposition

        queue = [nd for nd in g.tree.nodes]
        bag_copy = None

        while True:
            if g.validate(hypergraph):
                break

            if len(queue) == 0:
                break

            if bag_copy is not None:
                g.bags = bag_copy

            r = queue.pop()
            g.tree = DiGraph()
            g.tree.add_node(r)
            bag_copy = {}
            for k, v in g.bags.iteritems():
                bag_copy[k] = set(v)

            dfs_q = [r]

            while dfs_q:
                c_n = dfs_q.pop()
                for o_n in ug.neighbors(c_n):
                    if o_n not in g.tree.nodes:
                        g.tree.add_edge(c_n, o_n)
                        dfs_q.append(o_n)

            changed = True
            while changed:
                changed = False
                for u in g.tree.nodes:
                    T_u = dfs_tree(g.tree, u)
                    vertices_in_bags_below_u = set()
                    for t in T_u.nodes():
                        vertices_in_bags_below_u.update(g.bags[t])
                    missing = (vertices_in_bags_below_u & g._B(u)) - g.bags[u]
                    if len(missing) > 0:
                        g.bags[u].update(missing)
                        changed = True

                changed = changed or g.repair_connectedness()
        return g

    def repair_connectedness(self):
        w = self.width()
        changed = False
        for t in self.tree.nodes():
            t_b = self._B(t)
            if not (self.bags[t] <= t_b):
                width = sum(self.hyperedge_function[t].itervalues())

                # Verify that we do not change the result by adding edges
                if w - width > 0:
                    changed = True

                    residue = self.bags[t] - t_b
                    val = w - width
                    while val > 0 and len(residue) > 0:
                        # Try to find an edge that covers as many of the sought vertices as possible (heuristic)
                        # Idea: on a tie, use the edge that would add the least amount of covered vertices?
                        e = None
                        e_val = -1
                        for cE in (x for x, v in self.hyperedge_function[t].iteritems() if v == 0):
                            eVal = len(set(self.hypergraph.get_edge(cE)) & residue)

                            if eVal > e_val:
                                e_val = eVal
                                e = cE

                        # Add the hyperedge
                        self.hyperedge_function[t][e] = 1
                        residue = residue - set(self.hypergraph.get_edge(e))
                        val -= 1

    def construct_tree2(self, edges, primal, ordering, arcs):

        # # Test, find hierarchy
        # q = list(self.tree.nodes)
        # q2 = list()
        # hierarchy = {0: set()}
        # while q:
        #     cn = q.pop()
        #     children = list(self.tree.predecessors(cn))
        #
        #     found = True
        #     maxval = -1
        #     for cc in children:
        #         found2 = False
        #         for kk, kv in hierarchy.iteritems():
        #             if cc in kv:
        #                 maxval = max(maxval, kk)
        #                 found2 = True
        #                 break
        #
        #         if not found2:
        #             found = False
        #             break
        #
        #     if found:
        #         if maxval + 1 not in hierarchy:
        #             hierarchy[maxval + 1] = set()
        #         hierarchy[maxval + 1].add(cn)
        #     else:
        #         q2.append(cn)
        #
        #     if not q:
        #         q = q2
        #         q2 = list()

        self.tree = DiGraph()
        for i, j in edges:
            self.tree.add_edge(i, j)

        smallest = lambda A: min([(ordering.index(xi), xi) for xi in A])

        bags = {v: set() for v in primal.nodes()}
        # for i in ordering:
        #     bags[i] = set()
        #     bags[i].add(i)
        #     for j in ordering:
        #         if arcs[i][j]:
        #             bags[i].add(j)
        # self.bags = bags
        # return
        cvd = {n: set() for n in self.tree.nodes}
        for cid in self.hypergraph.edge_ids_iter():
            for n in self.tree.nodes:
                if self.hyperedge_function[n][cid] == 1:
                    cvd[n].update(self.hypergraph.get_edge(cid))

        for e in primal.edges():
            cs = set(e)
            found = False
            while cs and not found:
                cn = smallest(cs)[1]
                cs.remove(cn)
                res = [x for x in e if x not in arcs[cn]]
                if len(res) == 0 or (len(res) == 1 and res[1] == cn):
                    found = True
                    bags[cn].update(e)

                    # Just check
                    if any((x not in cvd[cn] for x in e)):
                        sys.stdout.write("The edge is not covered...\n")

            if not found:
                sys.stdout.write("Could not fill bag...\n")

        # Bottom up
        rordering = reversed(ordering)
        def cmp(i, j):
            if ordering.index(i) > ordering.index(j):
                return 1
            else:
                return -1

        updated = True
        while updated:
            updated = False
            for cn in rordering:
                anc = list(ancestors(self.tree, cn))
                anc = sorted(anc, cmp=cmp)

                for ca in anc:
                    path = [x for x in shortest_path(self.tree, ca, cn) if x != ca and x != cn]

                    # Check HTD condition
                    diff = set((bags[cn] - bags[ca]) & cvd[ca])
                    # if len(diff - bags[ca]) > 0:
                    #     bags[ca].update(diff)
                    #     updated = True

                    # Check decomposition condition
                    com = set(bags[cn] & bags[ca])
                    for cp in path:
                        if len(com - bags[cp]) > 0:
                            if len((com - bags[cp]) - cvd[cp]) > 0:
                                sys.stdout.write("Found non coverable entry\n")
                            bags[cp].update(com)
                            updated = True

        # for e in primal.edges():
        #     bags[smallest(e)[1]].update(e)
        #
        # for v in ordering:
        #     # copy
        #     A = set(bags[v])  # - v
        #
        #     if len(A) > 1:
        #         A.remove(v)
        #
        #         nxt = nxtn(v, A)
        #         children = set(self.tree.predecessors(v))
        #         parent = list(self.tree.successors(v))
        #
        #         if len(parent) > 1:
        #             sys.stdout.write("Found node with more than one parent...\n")
        #
        #         if len(children) > 0:
        #             if nxt not in children:
        #                 sys.stdout.write("Next differs".format(parent[0], nxt, v))
        #
        #             for cc in children:
        #                 bags[cc].update(A)

        self.bags = bags

    def construct_tree(self, edges, primal, ordering, arcs):
        self.tree = DiGraph()
        for i, j in edges:
            self.tree.add_edge(i, j)

        smallest = lambda A: min([(ordering.index(xi), xi) for xi in A])
        bags = {v: set() for v in primal.nodes()}
        cvd = {n: set() for n in self.tree.nodes}
        for cid in self.hypergraph.edge_ids_iter():
            for n in self.tree.nodes:
                if self.hyperedge_function[n][cid] == 1:
                    cvd[n].update(self.hypergraph.get_edge(cid))

        for i in self.tree.nodes:
            if i not in cvd[i]:
                print "Failed for an i"
            bags[i].update(x for x in cvd[i] if (x == i or arcs[i][x]))

        # Bottom up
        rordering = list(reversed(ordering))

        def cmp(i, j):
            if ordering.index(i) > ordering.index(j):
                return 1
            else:
                return -1

        ecover = {x: set() for x in self.hypergraph.edge_ids_iter()}
        for ce in ecover.iterkeys():
            e = self.hypergraph.get_edge(ce)
            for kk, kv in bags.iteritems():
                if len(set(e) - kv) == 0:
                    ecover[ce].add(kk)

        # _edge_ids_where_v_occurs

        shares = {x: set() for x in self.tree.nodes}
        for cn in self.tree.nodes:
            for kk, kv in bags.iteritems():
                if kk != cn:
                    if len(bags[kk] & kv) > 0:
                        shares[cn].add(kk)

        updated = True
        while updated:
            updated = False
            for cn in rordering:
                anc = list(ancestors(self.tree, cn))
                anc = sorted(anc, cmp=cmp)

                path = []
                for ca in anc:
                    #path = [x for x in shortest_path(self.tree, ca, cn) if x != ca and x != cn]

                    # Check HTD condition
                    diff = set((bags[cn] - bags[ca]) & cvd[ca])
                    # if len(diff - bags[ca]) > 0:
                    #     bags[ca].update(diff)
                    #     updated = True

                    # Check decomposition condition
                    com = set(bags[cn] & bags[ca])
                    for cp in path:
                        prob = com - bags[cp]
                        for x in prob:
                            if not (self.try_remove(bags, ecover, x, cn) or self.try_remove(bags, ecover, x, ca)):
                                sys.stdout.write("Found non-coverable entry\n")
                            else:
                                com.remove(x)

                            # updated = True
                    path.append(ca)

        # Find those violations, where bags in two different branches share a variable
        # but the lowest common ancestor does not share the variable
        for kk in rordering:
            for cv in shares[kk]:
                anc = lowest_common_ancestor(self.tree, kk, cv)
                com = bags[kk] & bags[cv]

                if len(com - bags[anc]) > 0:
                    prob = com - bags[anc]
                    for x in prob:
                        if not (self.try_remove(bags, ecover, x, kk) or self.try_remove(bags, ecover, x, cv)):
                            sys.stdout.write("Found violation at nodes {} {}, bags {} ; {} ; Problem: {}\n".format(kk, cv, bags[kk], bags[cv], prob))

        # for e in primal.edges():
        #     cs = set(e)
        #     found = False
        #     while cs and not found:
        #         cn = smallest(cs)[1]
        #         cs.remove(cn)
        #         res = [x for x in e if x not in arcs[cn]]
        #         if len(res) == 0 or (len(res) == 1 and res[1] == cn):
        #             found = True
        #             bags[cn].update(e)
        #
        #             # Just check
        #             if any((x not in cvd[cn] for x in e)):
        #                 sys.stdout.write("The edge is not covered...\n")
        #
        #     if not found:
        #         sys.stdout.write("Could not fill bag...\n")
        #
        # # Bottom up
        # rordering = reversed(ordering)
        # def cmp(i, j):
        #     if ordering.index(i) > ordering.index(j):
        #         return 1
        #     else:
        #         return -1
        #
        # updated = True
        # while updated:
        #     updated = False
        #     for cn in rordering:
        #         anc = list(ancestors(self.tree, cn))
        #         anc = sorted(anc, cmp=cmp)
        #
        #         for ca in anc:
        #             path = [x for x in shortest_path(self.tree, ca, cn) if x != ca and x != cn]
        #
        #             # Check HTD condition
        #             diff = set((bags[cn] - bags[ca]) & cvd[ca])
        #             # if len(diff - bags[ca]) > 0:
        #             #     bags[ca].update(diff)
        #             #     updated = True
        #
        #             # Check decomposition condition
        #             com = set(bags[cn] & bags[ca])
        #             for cp in path:
        #                 if len(com - bags[cp]) > 0:
        #                     if len((com - bags[cp]) - cvd[cp]) > 0:
        #                         sys.stdout.write("Found non coverable entry\n")
        #                     bags[cp].update(com)
        #                     updated = True

        # for e in primal.edges():
        #     bags[smallest(e)[1]].update(e)
        #
        # for v in ordering:
        #     # copy
        #     A = set(bags[v])  # - v
        #
        #     if len(A) > 1:
        #         A.remove(v)
        #
        #         nxt = nxtn(v, A)
        #         children = set(self.tree.predecessors(v))
        #         parent = list(self.tree.successors(v))
        #
        #         if len(parent) > 1:
        #             sys.stdout.write("Found node with more than one parent...\n")
        #
        #         if len(children) > 0:
        #             if nxt not in children:
        #                 sys.stdout.write("Next differs".format(parent[0], nxt, v))
        #
        #             for cc in children:
        #                 bags[cc].update(A)

        self.bags = bags

    def try_remove(self, bags, ecover, target, node):
        es = self._edge_ids_where_v_occurs(target)

        if all((node not in ecover[ce] or len(ecover[ce]) > 1) for ce in es):
            bags[node].remove(target)

            for ce in es:
                ecover[ce].discard(node)

            return True

        return False

    def inverse_edge_function_holds(self):
        logging.info('=' * 80)
        logging.info('Inverse edge function property')
        logging.info('=' * 80)
        for u in self.tree.nodes:
            T_u = dfs_tree(self.tree, u)
            vertices_in_bags_below_u = set()
            for t in T_u.nodes():
                vertices_in_bags_below_u.update(self.bags[t])
            if not (vertices_in_bags_below_u & self._B(u) <= self.bags[u]):
                logging.error('Inverse edge function property does not hold for node "%s"' % u)
                logging.error('Bag of the subtree induced at "%s" contained "%s"' % (u, vertices_in_bags_below_u))
                logging.error('Vertices returned from the edge function are "%s"' % self._B(u))
                logging.error('Bag content is: %s' % self.bags[u])
                logging.error(
                    'Hence, not (vertices_in_bags_below_u & self._B(u) <= self.bags[u]) does not hold for node %s.' % u)
                return False
        logging.info('Inverse edge function property *holds*.')
        logging.info('=' * 80)
        return True

    def validate(self, graph, strict=True):
        self.hypergraph = graph
        if self.is_tree(
                strict=strict) and self.edges_covered() and self.is_connected() and self.edge_function_holds() and \
                self.inverse_edge_function_holds():
            return True
        else:
            logging.error('ERROR in Tree Decomposition.')
            return False

    def __str__(self):
        string = StringIO()
        self.write(string)
        return string.getvalue()
