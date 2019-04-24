import logging
import os
import traceback
from cStringIO import StringIO
from collections import defaultdict
from itertools import chain

import htd_validate.utils.relabelling as relab
import networkx as nx
from htd_validate.utils import HypergraphPrimalView
from networkx.drawing.nx_agraph import graphviz_layout


class Decomposition(object):
    _problem_string = 'missing'
    _data_type = int

    def __new__(cls, *args, **kwargs):
        if cls is Decomposition:
            raise TypeError("base class may not be instantiated")
        return object.__new__(cls)

    @property
    def chi(self):
        return self.bags

    @property
    def T(self):
        return self.tree

    @property
    def graph(self):
        return self.hypergraph

    def set_graph(self, hypergraph):
        self.hypergraph = hypergraph

    def findIntersectingBag(self, edge):
        tdinter = None
        tdfound = None
        for i, b in self.bags.iteritems():
            tdinter = b.intersection(edge)
            if len(tdinter) > 0:
                tdfound = i
                break
        return tdfound, tdinter

    def connect(self, td, edge=None, edge_id=None):
        assert ((edge is None) == (edge_id is None))
        assert (edge is None or len(edge) <= 2)

        tdfound = None
        selffound = None

        t2 = self.tree.number_of_nodes()
        if edge is not None:
            tdfound = td.findIntersectingBag(edge)[0]
            selffound = self.findIntersectingBag(edge)[0]
            if tdfound is None or selffound is None:
                return False
            tdfound += t2  # relabelling

            if len(edge) > 1:
                t2 += 1
                self.bags[t2] = set(edge)
                self.tree.add_node(t2)
                self.tree.add_edge(selffound, t2)
                self._connect(t2, edge_id)
        else:
            selffound = list(self.tree.nodes())[0]
            tdfound = t2 + list(td.T.nodes())[0]

        # copy / relabel TD nodes
        for v in td.T.nodes():
            self.tree.add_node(t2 + v)
            self.bags[t2 + v] = td.chi[v]
            self._connect_weights(t2 + v, v, td)
        for e in td.T.edges():
            self.tree.add_edge(t2 + e[0], t2 + e[1])

        if edge is not None and len(edge) > 1:
            self.tree.add_edge(t2, tdfound)
        else:
            self.tree.add_edge(selffound, tdfound)
        return True

    def _connect_weights(self, t, old_t, td):
        pass

    def _connect(self, t, edge_id):
        pass

    @classmethod
    def _from_ordering(cls, hypergraph, plot_if_td_invalid=True, ordering=None, weights=None, checker_epsilon=None):
        if ordering is None:
            ordering = sorted(hypergraph.nodes())

        tree = nx.DiGraph()
        # use lex smallest, python first compares first pos of tuple
        smallest = lambda x: min([(ordering.index(xi), xi) for xi in x])

        # initialize with empty bags
        chi = {v: set() for v in hypergraph.nodes()}
        tree.add_nodes_from(range(1, hypergraph.number_of_nodes() + 1))

        for e in hypergraph.edges():
            chi[smallest(e)[1]].update(e)

        for v in ordering:
            # copy
            A = set(chi[v])  # - v

            if len(A) > 1:
                logging.debug("A(before-rem) = %s" % A)
                A.remove(v)
                logging.debug("A(after-rem) = %s" % A)
                nxt = smallest(A)[1]
                logging.debug("nxt =%s, v=%s, A=%s, chi[nxt]=%s" % (nxt, v, A, chi[nxt]))
                chi[nxt].update(A)
                logging.debug("chi[nxt]=%s" % chi[nxt])
                tree.add_edge(nxt, v)
        ret = cls(hypergraph=hypergraph, plot_if_td_invalid=plot_if_td_invalid, tree=tree, bags=chi,
                  hyperedge_function=weights, epsilon=checker_epsilon)
        return ret

    def replay(self, repl):
        assert (repl is not None)
        assert (self.graph is not None)
        repl.reverse()  # redo repl in reverse order
        for (parent, bag, weight) in repl:
            logging.info("searching for {0},{1},{2}".format(parent, bag, weight))
            found = False
            for t in list(self.tree.nodes()):
                # print self.bags[t]
                if self.bags[t].issuperset(parent):
                    t2 = self.tree.number_of_nodes() + 1
                    self.tree.add_node(t2)
                    self.tree.add_edge(t, t2)
                    parent = set(parent)
                    parent.update(bag)
                    self.bags[t2] = parent  # set(bag)
                    self._replay(t2, parent,
                                 weight)  # TODO: use additional stored weight info, instead of recomputation
                    found = True
            if not found:
                assert (len(parent) == 0)
                assert (len(self.tree.nodes()) == 0)
                t2 = 1
                self.tree.add_node(t2)
                self.bags[t2] = set(bag)
                self._replay(t2, bag, weight)  # TODO: use additional stored weight info, instead of recomputation
                # found = True
            # assert(found)

    def _replay(self, node, bag, weight):
        pass

    def __init__(self, hypergraph=None, plot_if_td_invalid=True, tree=None, bags=None, hyperedge_function=None,
                 checker_epsilon=None):
        if checker_epsilon:
            self.__epsilon = checker_epsilon
        if tree is None:
            tree = nx.DiGraph()
        if bags is None:
            bags = {}
        if hyperedge_function:
            self.hyperedge_function = hyperedge_function

        self.tree = tree
        self.bags = bags
        self.hypergraph = hypergraph
        self.plot_if_td_invalid = plot_if_td_invalid

    @staticmethod
    def graph_type():
        raise NotImplementedError("abstract method -- subclass must override")

    def __len__(self):
        return len(self.bags)

    @classmethod
    def from_file(cls, filename, strict=False):
        """
        :param strict: strictly enforce PACE requirements for the input format (pace specs are unnecessarily strict)
        :param filename:
        :rtype: TreeDecomposition
        :return:
        """
        header_seen = False
        nr = 0

        def log_critical(string):
            logging.critical('%s:L(%s). %s  Exiting...' % (os.path.basename(filename), nr, string))

        decomp = cls()
        with open(filename, 'r') as fobj:
            num_bags = num_vertices = 0
            header = {}
            try:
                edge_seen = False
                for line in fobj.readlines():
                    line = line.split()
                    nr = nr + 1
                    # noinspection PySimplifyBooleanCheck
                    if line == []:
                        continue
                    if line[0] == 'c':
                        logging.info('-' * 20 + 'INFO from decomposition reader' + '-' * 20)
                        logging.info('%s' % ' '.join(line))
                        logging.info('-' * 80)
                        continue
                    elif line[0] == 's' and line[1] == cls._problem_string:
                        if header_seen:
                            log_critical('Duplicate header.')
                            exit(2)
                        try:
                            header['num_bags'] = int(line[2])
                            header['num_vertices'] = int(line[4])
                            header.update(cls._read_header(line))
                        except ValueError as e:
                            logging.error(e)
                            log_critical('Too many or too few arguments in header.')
                            exit(2)
                        header_seen = True
                    elif line[0] == 'b':
                        if not header_seen:
                            log_critical('Bag before header.')
                            exit(2)
                        if strict and edge_seen:
                            log_critical('Edge before bag.')
                            exit(2)
                        if len(line) < 2:
                            log_critical('Some bag has no index.')
                            exit(1)
                        if strict and len(line) < 3:
                            log_critical('Empty bag.')
                            exit(2)
                        bag_name = int(line[1])
                        if decomp.bags.has_key(bag_name):
                            log_critical('Duplicate bag.')
                            exit(2)
                        # TODO: implement type checking for htd|fhtd
                        # TODO: BUT NOT HERE! type checking required in 'w' line ~> _reader
                        try:
                            decomp.bags[bag_name] = set(map(int, line[2:]))
                        except ValueError as e:
                            log_critical("Type checking failed (expected %s)." % int)  # cls._data_type)
                            logging.critical("Full exception %s." % e)
                            exit(2)
                        decomp.tree.add_node(bag_name)
                    else:
                        if cls._reader(decomp, line):
                            continue
                        else:
                            if strict and not header_seen:
                                log_critical('Edge before header.')
                                exit(2)
                            u, v = map(int, line)
                            if u > header['num_bags']:
                                log_critical("Edge label %s out of bounds (expected max %s bags)." % (u, num_bags))
                                exit(2)
                            if v > header['num_bags']:
                                log_critical("Edge label %s out of bounds (expected max %s bags)." % (v, num_bags))
                                exit(2)
                            if u not in decomp.bags.keys():
                                log_critical(
                                    "Edge in the tree (%s,%s) without a corresponding bag for node %s." % (u, v, u))
                                exit(2)
                            if v not in decomp.bags.keys():
                                log_critical(
                                    "Edge in the tree (%s,%s) without a corresponding bag for node %s." % (u, v, v))
                                exit(2)
                            decomp.tree.add_edge(u, v)
                            edge_seen = True
            except ValueError as e:
                logging.critical("Undefined input.")
                logging.critical(e)
                logging.warning("Output was:")
                fobj.seek(0)
                for line in fobj.readlines():
                    logging.warning(line)
                for line in traceback.format_exc().split('\n'):
                    logging.critical(line)
                logging.critical('Exiting...')
                exit(143)
            # decomps of single bags require special treatment
            if not header_seen:
                logging.critical('Missing header. Exiting...')
                exit(2)
            if len(decomp) == 1:
                # noinspection PyUnresolvedReferences
                decomp.tree.add_node(decomp.bags.iterkeys().next())
            if decomp.specific_valiation(decomp, header):
                logging.critical('Decomposition specific validation failed.')
                exit(2)
            if len(decomp) != header['num_bags']:
                logging.critical('Number of bags differ. Was %s expected %s.\n' % (len(decomp), header['num_bags']))
                exit(2)
            if decomp.num_vertices > header['num_vertices']:
                logging.critical(
                    'Number of vertices differ (>). Was %s expected %s.\n' % (
                        decomp.num_vertices, header['num_vertices']))
                exit(2)
            if decomp.num_vertices < header['num_vertices'] and strict:
                logging.warning(
                    'Number of vertices differ (<). Was %s expected %s.\n' % (decomp.num_vertices, num_vertices))
                exit(2)
        return decomp

    def edges_covered(self):
        # initialise with edges
        # TODO: something missing here
        covered_edges = {e: False for e in self.hypergraph.edges_iter()}
        for e in self.hypergraph.edges_iter():
            if not any(set(e) <= bag for bag in self.bags.itervalues()):
                logging.error('Edge "%s" is not covered in any bag.' % str(e))
                return False
        return True

    def is_tree(self, strict=True):
        ret = len(self.tree) == 0 or nx.is_tree(self.tree)
        if not ret:
            logging.warning('The underlying graph is not a tree.')
        if not strict and not ret:
            ret = nx.is_directed_acyclic_graph(self.tree)
        if not ret:
            logging.error('The underlying graph is not a tree.')
        return ret

    def bag_occuences(self):
        vertex2bags = defaultdict(set)
        for n, bag in self.bags.iteritems():
            for v in bag:
                vertex2bags[v].add(n)
        logging.debug('Bag occurences yields: %s' % vertex2bags)
        return vertex2bags

    def is_connected(self):
        vertex2bags = self.bag_occuences()
        # print self.hypergraph.number_of_edges()
        for v in self.hypergraph.nodes_iter():
            logging.debug("vertex %s" % v)
            SG = self.tree.subgraph(vertex2bags[v])
            if not nx.is_connected(SG.to_undirected()):
                logging.error('Subgraph induced by vertex "%s" is not connected' % v)
                string = StringIO()
                nx.write_multiline_adjlist(SG, string)
                logging.error('Involved bags: %s' % vertex2bags[v])
                logging.error('Nodes of the hypergraph (should be the same): %s' % SG.nodes())
                logging.error('Begin Adjacency Matrix')
                # we skip comments from networkx
                for line in string.getvalue().split('\n')[3:-1]:
                    logging.error('%s' % line)
                logging.error('End Adjacency Matrix')
                return False
        return True

    @property
    def num_vertices(self):
        return len(set(chain.from_iterable(self.bags.itervalues())))

    @staticmethod
    def specific_valiation(td, problem_statement):
        raise NotImplementedError("abstract method -- subclass must override")

    @staticmethod
    def _reader(decomp, line):
        raise NotImplementedError("abstract method -- subclass must override")

    def relabel(self, substitution, substitution_edges):
        self.bags = relab.relabel_dict(self.bags, substitution, typ=set)
        # print self.bags
        # assert(len(self.bags) == 0)
        self._relabel(substitution_edges)

    def _relabel(self, substitution_edges):
        pass

    @staticmethod
    def _read_header(line):
        raise NotImplementedError("abstract method -- subclass must override")

    def show(self, layout, nolabel=0):
        """ show hypergraph
        layout 1:graphviz,
        2:circular,
        3:spring,
        4:spectral,
        5: random,
        6: shell
        """
        if not self.plot_if_td_invalid:
            logging.error('written_decomp(tree)=%s', self.tree.edges())
            logging.error('written_decomp(bags)=%s', self.bags)

            return
        else:
            import matplotlib.pyplot as plt
            import matplotlib

            m = self.tree.copy()

            hg = HypergraphPrimalView(hypergraph=self.hypergraph)
            pos = self.layouting(layout=2, m=m)
            # nx.draw_networkx_nodes(hg, pos)
            nx.draw(hg, pos)
            plt.show()

            plt.figure(num=None, figsize=(20, 20), dpi=80)

            # matplotlib.use('TkAgg')
            import warnings
            warnings.filterwarnings("ignore", category=matplotlib.cbook.mplDeprecation)

            pos = self.layouting(layout, m)

            if not nolabel:
                nx.draw_networkx_edge_labels(m, pos)
            nx.draw_networkx_nodes(m, pos)
            if self.bags:
                # bags = {k: '%s:%s' % (k, str(sorted(list(v)))) for k, v in self.bags.iteritems()}
                bags = {}
                logging.info("hyperedge_function %s" % self.hyperedge_function)

                for k, v in self.bags.iteritems():
                    if self.hyperedge_function:
                        w = ','.join(
                            str(l) + '\n' * (n % 4 == 3) for n, l in enumerate(self.hyperedge_function[k].values()))
                        bags[k] = '%s:%s\n%s' % (k, str(sorted(list(v))), w)
                    else:
                        bags[k] = '%s:%s' % (k, str(sorted(list(v))))
                nx.draw_networkx_labels(m, pos, bags)
            else:
                nx.draw_networkx_labels(m, pos)
            nx.draw(m, pos)
            plt.show()

    @staticmethod
    def layouting(layout, m):
        pos = graphviz_layout(m)
        if layout == 1:
            pos = graphviz_layout(m)
        elif layout == 2:
            pos = nx.circular_layout(m)
        elif layout == 3:
            pos = nx.spring_layout(m)
        elif layout == 4:
            pos = nx.spectral_layout(m)
        elif layout == 5:
            pos = nx.random_layout(m)
        elif layout == 6:
            pos = nx.shell_layout(m)
        return pos
