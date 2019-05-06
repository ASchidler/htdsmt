import logging
from cStringIO import StringIO

from htd_validate.decompositions import GeneralizedHypertreeDecomposition
from htd_validate.utils import Hypergraph, HypergraphPrimalView
from networkx.algorithms.traversal.depth_first_search import dfs_tree
from networkx import DiGraph


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
    def from_ordering(cls, hypergraph, ordering=None, weights=None, checker_epsilon=None):
        pgraph_view = HypergraphPrimalView(hypergraph=hypergraph)
        g = cls._from_ordering(hypergraph=pgraph_view, plot_if_td_invalid=False, ordering=ordering, weights=weights,
                                  checker_epsilon=checker_epsilon)

        g.hypergraph = hypergraph
        # For the HTD the root is important. Try to find a root, that
        ug = g.tree.to_undirected()

        r = None
        # Find current r
        for c_node in g.tree.nodes:
            if g.tree.in_degree(c_node) == 0:
                r = c_node
                break

        # We have a ghtd, now try to repair it to a htd
        # Try each node as a root. Next try to repair the bags. This may not yield a valid decomposition
        queue = [nd for nd in g.tree.nodes if nd != r]
        bag_copy = None
        while True:
            if g.validate(hypergraph):
                break

            if bag_copy is not None:
                g.bags = bag_copy

            if len(queue) == 0:
                break

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

        return g

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
