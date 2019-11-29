#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2018
# Johannes K. Fichte, TU Wien, Austria*
# Markus A. Hecher, TU Wien, Austria*
#
# *) also affiliated with University of Potsdam(R) :P
#
# hypergraph.py is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.  hypergraph.py is distributed in
# the hope that it will be useful, but WITHOUT ANY WARRANTY; without
# even the implied warranty of MERCHANTABILITY or FITNESS FOR A
# PARTICULAR PURPOSE.  See the GNU General Public License for more
# details.  You should have received a copy of the GNU General Public
# License along with hypergraph.py.  If not, see
# <http://www.gnu.org/licenses/>.
# from __future__ import print_function

# import cplex
import copy
import subprocess

import networkx as nx
from lib.htd_validate.htd_validate.utils.formula import Formula
from lib.htd_validate.htd_validate.utils.hypergraph import Hypergraph


class HypergraphPrimalView(object):
    # (nx.graph):
    # #https://networkx.github.io/documentation/networkx-1.11/_modules/networkx/classes/graph.html#Graph

    def __init__(self, hypergraph):
        # super(HypergraphPrimalView, self).__init__()
        self.__hg = hypergraph

    @property
    def hg(self):
        return self.__hg

    @property
    def name(self):
        raise NotImplementedError()

    @name.setter
    def name(self, s):
        raise NotImplementedError()

    def __copy__(self):
        return HypergraphPrimalView(copy.copy(self.__hg))

    def __deepcopy__(self, memodict=None):
        if memodict is None:
            memodict = {}
        return HypergraphPrimalView(copy.deepcopy(self.__hg, memodict))

    def induced_graph(self, v, force_copy=False):
        if not force_copy and self.hg.nodes() == set(v):
            return self
        h = Hypergraph(vertices=v)
        h.induce_edges(self.__hg.edges())
        return HypergraphPrimalView(h)

    def __str__(self):
        return str(self.__hg)

    def __iter__(self):
        """Iterate over the nodes. Use the expression 'for n in G'.

        Returns
        -------
        niter : iterator
            An iterator over all nodes in the graph.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        """
        return self.__hg.nodes_iter()

    def __contains__(self, n):
        """Return True if n is a node, False otherwise. Use the expression
        'n in G'.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> 1 in G
        True
        """
        try:
            return n in self.__hg
        except TypeError:
            return False

    def __len__(self):
        """Return the number of nodes. Use the expression 'len(G)'.

        Returns
        -------
        nnodes : int
            The number of nodes in the graph.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> len(G)
        4

        """
        return len(self.__hg)

    def __getitem__(self, n):
        """Return a dict of neighbors of node n.  Use the expression 'G[n]'.

        Parameters
        ----------
        n : node
           A node in the graph.

        Returns
        -------
        adj_dict : dictionary
           The adjacency dictionary for nodes connected to n.

        Notes
        -----
        G[n] is similar to G.neighbors(n) but the internal data dictionary
        is returned instead of a list.

        Assigning G[n] will corrupt the internal graph data structure.
        Use G[n] for reading data only.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G[0]
        {1: {}}
        """
        return self.__hg.adjByNode(n)

    def add_node(self, n, attr_dict=None, **attr):
        """Add a single node n and update node attributes.

        Parameters
        ----------
        n : node
            A node can be any hashable Python object except None.
        attr_dict : dictionary, optional (default= no attributes)
            Dictionary of node attributes.  Key/value pairs will
            update existing data associated with the node.
        attr : keyword arguments, optional
            Set or change attributes using key=value.

        See Also
        --------
        add_nodes_from

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_node(1)
        >>> G.add_node('Hello')
        >>> K3 = nx.Graph([(0,1),(1,2),(2,0)])
        >>> G.add_node(K3)
        >>> G.number_of_nodes()
        3

        Use keywords set/change node attributes:

        >>> G.add_node(1,size=10)
        >>> G.add_node(3,weight=0.4,UTM=('13S',382871,3972649))

        Notes
        -----
        A hashable object is one that can be used as a key in a Python
        dictionary. This includes strings, numbers, tuples of strings
        and numbers, etc.

        On many platforms hashable items also include mutables such as
        NetworkX Graphs, though one should be careful that the hash
        doesn't change on mutables.
        """
        raise NotImplementedError()

    def add_nodes_from(self, nodes, **attr):
        """Add multiple nodes.

        Parameters
        ----------
        nodes : iterable container
            A container of nodes (list, dict, set, etc.).
            OR
            A container of (node, attribute dict) tuples.
            Node attributes are updated using the attribute dict.
        attr : keyword arguments, optional (default= no attributes)
            Update attributes for all nodes in nodes.
            Node attributes specified in nodes as a tuple
            take precedence over attributes specified generally.

        See Also
        --------
        add_node

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_nodes_from('Hello')
        >>> K3 = nx.Graph([(0,1),(1,2),(2,0)])
        >>> G.add_nodes_from(K3)
        >>> sorted(G.nodes(),key=str)
        [0, 1, 2, 'H', 'e', 'l', 'o']

        Use keywords to update specific node attributes for every node.

        >>> G.add_nodes_from([1,2], size=10)
        >>> G.add_nodes_from([3,4], weight=0.4)

        Use (node, attrdict) tuples to update attributes for specific
        nodes.

        >>> G.add_nodes_from([(1,dict(size=11)), (2,{'color':'blue'})])
        >>> G.node[1]['size']
        11
        >>> H = nx.Graph()
        >>> H.add_nodes_from(G.nodes(data=True))
        >>> H.node[1]['size']
        11

        """
        raise NotImplementedError()

    def remove_node(self, n):
        """Remove node n.

        Removes the node n and all adjacent edges.
        Attempting to remove a non-existent node will raise an exception.

        Parameters
        ----------
        n : node
           A node in the graph

        Raises
        -------
        NetworkXError
           If n is not in the graph.

        See Also
        --------
        remove_nodes_from

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> G.edges()
        [(0, 1), (1, 2)]
        >>> G.remove_node(1)
        >>> G.edges()
        []

        """
        # adj = self.adj
        try:
            # nbrs = list(adjByNode[n].keys())  # keys handles self-loops (allow mutation later)
            del self.__hg[n]
        except KeyError:  # NetworkXError if n not in self
            raise nx.NetworkXError("The node %s is not in the graph." % (n,))
        # for u in nbrs:
        #    del adj[u][n]  # remove all edges n-u in graph
        # del adj[n]  # now remove node

    def __delitem__(self, v):
        self.remove_node(v)

    def remove_nodes_from(self, nodes):
        """Remove multiple nodes.

        Parameters
        ----------
        nodes : iterable container
            A container of nodes (list, dict, set, etc.).  If a node
            in the container is not in the graph it is silently
            ignored.

        See Also
        --------
        remove_node

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> e = G.nodes()
        >>> e
        [0, 1, 2]
        >>> G.remove_nodes_from(e)
        >>> G.nodes()
        []

        """
        # adj = self.adj
        for n in nodes:
            try:
                del self.__hg[n]
                # for u in list(adj[n].keys()):  # keys() handles self-loops
                #    del adj[u][n]  # (allows mutation of dict in loop)
                # del adj[n]
            except KeyError:
                pass

    # @deprecated("not tested; now replaced by ASP version in hypergraph")
    # @deprecation.deprecated(deprecated_in="1.0", removed_in="1.0",
    #                        current_version="1.0",
    #                        details="not tested; now replaced by ASP version for various reasons in Hypergraph")
    def largest_clique(self, solver=["glucose", "-model"], return_code_sat=10, timeout=None):

        clause = Formula()
        adj = self.__hg.adj

        sat = return_code_sat
        while sat == return_code_sat:

            p = subprocess.Popen(["glucose", "-model"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
            clause.stream = p.stdin
            # space for safety (clauses and variables need to be corrected later on)
            clause.writeHeader(safety=True)

            for u in self.nodes():
                for v in self.nodes():
                    if u < v and v not in adj[u]:
                        clause.addClause("-{0} -{1}".format(clause.map(u), clause.map(v)))

            for e in self.__hg.edges.values():
                # for k in xrange(3, len(e) + 1):
                # prevent 3 elements from the same edge

                k = 3
                sub = range(0, k)

                while True:  # sub[0] <= len(e) - k:

                    cl = ""
                    for v in sub:
                        cl.append(" -{0}".format(clause.map(e[v])))
                        clause.addClause(cl)

                    if sub[0] == len(e) - k:
                        break

                    # next position
                    for i in range(k - 1, -1, -1):
                        if sub[i] < len(e) - (k - i - 1):
                            sub[i] += 1
                            for j in range(i + 1, k):
                                sub[j] = sub[i] + (j - i)

            # seek to the file beginning and correct header
            clause.writeHeader()
            clause.close()

            sat = p.wait(timeout)

        for line in p.stdout:
            if line.startswith("v"):
                vals = line.split(" ")
                print(vals)

    # handle with care!
    # returns tuple (list of "almost" (depending on \emph{simplicial_diff}) simplicial vertices, clique) per clique
    # fixme: modify/replace nx.enumerate_all_cliques!
    def simplicial_iter(self, simplicial_diff=0, clique_prevent_he_at_least=3, clique_prevent_he_up_to=3):
        cl = None
        for k in range(clique_prevent_he_up_to, clique_prevent_he_at_least - 1, -1):
            maxcl = 0
            aset = self.__hg.largest_clique_asp(clingoctl=cl, prevent_k_hyperedge=k, ground=False)
            cl = aset[3]
            # print c
            # for clique in nx.enumerate_all_cliques(self) if not max_clique else self.__hg.largest_clique_asp()[2]:
            for clique in aset[2]:
                # if not max_clique and len(clique) > clique_sizes_up_to:
                #    return
                maxcl = max(maxcl, len(clique))
                # if clique_sizes_at_least <= len(clique): # <= clique_sizes_up_to:
                nodes_of_clique = []
                for c in clique:
                    simpl = self.degree(c) - len(clique) + 1
                    assert (simpl >= 0)
                    if simplicial_diff == simpl or 0 < simpl <= simplicial_diff:
                        nodes_of_clique.append((c, simpl))
                if k > 3 or len(nodes_of_clique) > 0:
                    yield (nodes_of_clique, clique, (k, maxcl))
            if k == 3:  # maybe we did not yield yet, get a chance now
                yield ([], [], (k, maxcl))
        # adj = self.__hg.adj
        # blacklist = set()
        # for k, a in adj:
        #     if k not in blacklist and clique_sizes_at_least <= len(a) <= clique_sizes_up_to:
        #         found = True
        #         for kk in a:
        #             a2 = adj[kk]
        #             if len(a2) == len(a):
        #                 for ai in a:
        #                     if ai not in adj[kk]:
        #                         blacklist.update(a)
        #                         found = False
        #
        #         if found:
        #             yield k

    def nodes_iter(self, data=False):
        """Return an iterator over the nodes.

        Parameters
        ----------
        data : boolean, optional (default=False)
               If False the iterator returns nodes.  If True
               return a two-tuple of node and node data dictionary

        Returns
        -------
        niter : iterator
            An iterator over nodes.  If data=True the iterator gives
            two-tuples containing (node, node data, dictionary)

        Notes
        -----
        If the node data is not required it is simpler and equivalent
        to use the expression 'for n in G'.

        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])

        >>> [d for n,d in G.nodes_iter(data=True)]
        [{}, {}, {}]
        """
        if data:
            raise NotImplementedError()
            # return iter(self.node.items())
        return self.__hg.nodes_iter()

    def nodes(self, data=False):
        """Return a list of the nodes in the graph.

        Parameters
        ----------
        data : boolean, optional (default=False)
               If False return a list of nodes.  If True return a
               two-tuple of node and node data dictionary

        Returns
        -------
        nlist : list
            A list of nodes.  If data=True a list of two-tuples containing
            (node, node data dictionary).

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> G.nodes()
        [0, 1, 2]
        >>> G.add_node(1, time='5pm')
        >>> G.nodes(data=True)
        [(0, {}), (1, {'time': '5pm'}), (2, {})]
        """
        return list(self.nodes_iter(data=data))

    def number_of_nodes(self):
        """Return the number of nodes in the graph.

        Returns
        -------
        nnodes : int
            The number of nodes in the graph.

        See Also
        --------
        order, __len__  which are identical

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> len(G)
        3
        """
        return len(self.__hg)

    def order(self):
        """Return the number of nodes in the graph.

        Returns
        -------
        nnodes : int
            The number of nodes in the graph.

        See Also
        --------
        number_of_nodes, __len__  which are identical

        """
        return len(self.__hg)

    def has_node(self, n):
        """Return True if the graph contains the node n.

        Parameters
        ----------
        n : node

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> G.has_node(0)
        True

        It is more readable and simpler to use

        >>> 0 in G
        True

        """
        try:
            return n in self.__hg
        except TypeError:
            return False

    def add_edge(self, u, v, attr_dict=None, **attr):
        raise NotImplementedError()

    def add_edges_from(self, ebunch, attr_dict=None, **attr):
        raise NotImplementedError()

    def add_weighted_edges_from(self, ebunch, weight='weight', **attr):
        raise NotImplementedError()

    def remove_edge(self, u, v):
        raise NotImplementedError()

    def remove_edges_from(self, ebunch):
        raise NotImplementedError()

    def has_edge(self, u, v):
        """Return True if the edge (u,v) is in the graph.

        Parameters
        ----------
        u, v : nodes
            Nodes can be, for example, strings or numbers.
            Nodes must be hashable (and not None) Python objects.

        Returns
        -------
        edge_ind : bool
            True if edge is in the graph, False otherwise.

        Examples
        --------
        Can be called either using two nodes u,v or edge tuple (u,v)

        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.has_edge(0,1)  # using two nodes
        True
        >>> e = (0,1)
        >>> G.has_edge(*e)  #  e is a 2-tuple (u,v)
        True
        >>> e = (0,1,{'weight':7})
        >>> G.has_edge(*e[:2])  # e is a 3-tuple (u,v,data_dictionary)
        True

        The following syntax are all equivalent:

        >>> G.has_edge(0,1)
        True
        >>> 1 in G[0]  # though this gives KeyError if 0 not in G
        True

        """
        try:
            return v in self.__hg.adjByNode(u)
        except KeyError:
            return False
        # raise NotImplementedError()

    def neighbors(self, n, strict=True):
        """Return a list of the nodes connected to the node n.

        Parameters
        ----------
        n : node
           A node in the graph

        Returns
        -------
        nlist : list
            A list of nodes that are adjacent to n.

        Raises
        ------
        NetworkXError
            If the node n is not in the graph.

        Notes
        -----
        It is usually more convenient (and faster) to access the
        adjacency dictionary as G[n]:

        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_edge('a','b',weight=7)
        >>> G['a']
        {'b': {'weight': 7}}

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.neighbors(0)
        [1]

        """
        try:
            return self.__hg.adjByNode(n, strict=strict).keys()
        except KeyError:
            raise nx.NetworkXError("The node %s is not in the graph." % (n,))

    def neighbors_iter(self, n):
        """Return an iterator over all neighbors of node n.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> [n for n in G.neighbors_iter(0)]
        [1]

        Notes
        -----
        It is faster to use the idiom "in G[0]", e.g.

        >>> G = nx.path_graph(4)
        >>> [n for n in G[0]]
        [1]
        """
        try:
            return iter(self.__hg.adjByNode(n).keys())
        except KeyError:
            raise nx.NetworkXError("The node %s is not in the graph." % (n,))

    def edges(self, nbunch=None, data=False, default=None):
        """Return a list of edges.

        Edges are returned as tuples with optional data
        in the order (node, neighbor, data).

        Parameters
        ----------
        nbunch : iterable container, optional (default= all nodes)
            A container of nodes.  The container will be iterated
            through once.
        data : string or bool, optional (default=False)
            The edge attribute returned in 3-tuple (u,v,ddict[data]).
            If True, return edge attribute dict in 3-tuple (u,v,ddict).
            If False, return 2-tuple (u,v).
        default : value, optional (default=None)
            Value used for edges that dont have the requested attribute.
            Only relevant if data is not True or False.

        Returns
        --------
        edge_list: list of edge tuples
            Edges that are adjacent to any node in nbunch, or a list
            of all edges if nbunch is not specified.

        See Also
        --------
        edges_iter : return an iterator over the edges

        Notes
        -----
        Nodes in nbunch that are not in the graph will be (quietly) ignored.
        For directed graphs this returns the out-edges.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2])
        >>> G.add_edge(2,3,weight=5)
        >>> G.edges()
        [(0, 1), (1, 2), (2, 3)]
        >>> G.edges(data=True) # default edge data is {} (empty dictionary)
        [(0, 1, {}), (1, 2, {}), (2, 3, {'weight': 5})]
        >>> list(G.edges_iter(data='weight', default=1))
        [(0, 1, 1), (1, 2, 1), (2, 3, 5)]
        >>> G.edges([0,3])
        [(0, 1), (3, 2)]
        >>> G.edges(0)
        [(0, 1)]

        """
        return list(self.edges_iter(nbunch, data, default))

    def edges_iter(self, nbunch=None, data=False, default=None):
        """Return an iterator over the edges.

        Edges are returned as tuples with optional data
        in the order (node, neighbor, data).

        Parameters
        ----------
        nbunch : iterable container, optional (default= all nodes)
            A container of nodes.  The container will be iterated
            through once.
        data : string or bool, optional (default=False)
            The edge attribute returned in 3-tuple (u,v,ddict[data]).
            If True, return edge attribute dict in 3-tuple (u,v,ddict).
            If False, return 2-tuple (u,v).
        default : value, optional (default=None)
            Value used for edges that dont have the requested attribute.
            Only relevant if data is not True or False.

        Returns
        -------
        edge_iter : iterator
            An iterator of (u,v) or (u,v,d) tuples of edges.

        See Also
        --------
        edges : return a list of edges

        Notes
        -----
        Nodes in nbunch that are not in the graph will be (quietly) ignored.
        For directed graphs this returns the out-edges.

        Examples
        --------
        >>> G = nx.Graph()   # or MultiGraph, etc
        >>> G.add_path([0,1,2])
        >>> G.add_edge(2,3,weight=5)
        >>> [e for e in G.edges_iter()]
        [(0, 1), (1, 2), (2, 3)]
        >>> list(G.edges_iter(data=True)) # default data is {} (empty dict)
        [(0, 1, {}), (1, 2, {}), (2, 3, {'weight': 5})]
        >>> list(G.edges_iter(data='weight', default=1))
        [(0, 1, 1), (1, 2, 1), (2, 3, 5)]
        >>> list(G.edges_iter([0,3]))
        [(0, 1), (3, 2)]
        >>> list(G.edges_iter(0))
        [(0, 1)]

        """
        seen = {}  # helper dict to keep track of multiply stored edges
        if nbunch is None:
            nodes_nbrs = self.__hg.adj.items()
        else:
            nodes_nbrs = ((n, self.__hg.adjByNode[n]) for n in self.nbunch_iter(nbunch))
        if data is True:
            for n, nbrs in nodes_nbrs:
                for nbr, ddict in nbrs.items():
                    if nbr not in seen:
                        yield (n, nbr, ddict)
                seen[n] = 1
        elif data is not False:
            for n, nbrs in nodes_nbrs:
                for nbr, ddict in nbrs.items():
                    if nbr not in seen:
                        d = ddict[data] if data in ddict else default
                        yield (n, nbr, d)
                seen[n] = 1
        else:  # data is False
            for n, nbrs in nodes_nbrs:
                for nbr in nbrs:
                    if nbr not in seen:
                        yield (n, nbr)
                seen[n] = 1
        del seen

    def get_edge_data(self, u, v, default=None):
        """Return the attribute dictionary associated with edge (u,v).

        Parameters
        ----------
        u, v : nodes
        default:  any Python object (default=None)
            Value to return if the edge (u,v) is not found.

        Returns
        -------
        edge_dict : dictionary
            The edge attribute dictionary.

        Notes
        -----
        It is faster to use G[u][v].

        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G[0][1]
        {}

        Warning: Assigning G[u][v] corrupts the graph data structure.
        But it is safe to assign attributes to that dictionary,

        >>> G[0][1]['weight'] = 7
        >>> G[0][1]['weight']
        7
        >>> G[1][0]['weight']
        7

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.get_edge_data(0,1) # default edge data is {}
        {}
        >>> e = (0,1)
        >>> G.get_edge_data(*e) # tuple form
        {}
        >>> G.get_edge_data('a','b',default=0) # edge not in graph, return 0
        0
        """
        try:
            return self.__hg.adjByNode(u)[v]
        except KeyError:
            return default

    def adjacency_list(self):
        """Return an adjacency list representation of the graph.

        The output adjacency list is in the order of G.nodes().
        For directed graphs, only outgoing adjacencies are included.

        Returns
        -------
        adj_list : lists of lists
            The adjacency structure of the graph as a list of lists.

        See Also
        --------
        adjacency_iter

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.adjacency_list() # in order given by G.nodes()
        [[1], [0, 2], [1, 3], [2]]

        """
        return list(map(list, iter(self.__hg.adj.values())))

    def adjacency_iter(self):
        """Return an iterator of (node, adjacency dict) tuples for all nodes.

        This is the fastest way to look at every edge.
        For directed graphs, only outgoing adjacencies are included.

        Returns
        -------
        adj_iter : iterator
           An iterator of (node, adjacency dictionary) for all nodes in
           the graph.

        See Also
        --------
        adjacency_list

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> [(n,nbrdict) for n,nbrdict in G.adjacency_iter()]
        [(0, {1: {}}), (1, {0: {}, 2: {}}), (2, {1: {}, 3: {}}), (3, {2: {}})]

        """
        return iter(self.__hg.adj.items())

    def degree(self, nbunch=None, weight=None):
        """Return the degree of a node or nodes.

        The node degree is the number of edges adjacent to that node.

        Parameters
        ----------
        nbunch : iterable container, optional (default=all nodes)
            A container of nodes.  The container will be iterated
            through once.

        weight : string or None, optional (default=None)
           The edge attribute that holds the numerical value used
           as a weight.  If None, then each edge has weight 1.
           The degree is the sum of the edge weights adjacent to the node.

        Returns
        -------
        nd : dictionary, or number
            A dictionary with nodes as keys and degree as values or
            a number if a single node is specified.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.degree(0)
        1
        >>> G.degree([0,1])
        {0: 1, 1: 2}
        >>> list(G.degree([0,1]).values())
        [1, 2]

        """
        if nbunch in self:  # return a single node
            return next(self.degree_iter(nbunch, weight))[1]
        else:  # return a dict
            return dict(self.degree_iter(nbunch, weight))

    def biconnected_components(self):
        return nx.biconnected_components(self)
        # for b in nx.biconnected_components(self):
        #    yield b

    def degree_iter(self, nbunch=None, weight=None):
        """Return an iterator for (node, degree).

        The node degree is the number of edges adjacent to the node.

        Parameters
        ----------
        nbunch : iterable container, optional (default=all nodes)
            A container of nodes.  The container will be iterated
            through once.

        weight : string or None, optional (default=None)
           The edge attribute that holds the numerical value used
           as a weight.  If None, then each edge has weight 1.
           The degree is the sum of the edge weights adjacent to the node.

        Returns
        -------
        nd_iter : an iterator
            The iterator returns two-tuples of (node, degree).

        See Also
        --------
        degree

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> list(G.degree_iter(0)) # node 0 with degree 1
        [(0, 1)]
        >>> list(G.degree_iter([0,1]))
        [(0, 1), (1, 2)]

        """
        if nbunch is None:  # non lazy
            nodes_nbrs = self.__hg.adj.items()
        else:  # lazy
            nodes_nbrs = ((n, self.__hg.adjByNode(n)) for n in self.nbunch_iter(nbunch))

        if weight is None:
            for n, nbrs in nodes_nbrs:
                yield (n, len(nbrs) + (n in nbrs), nbrs)  # return tuple (n,degree)
        else:
            # edge weighted graph - degree is sum of nbr edge weights
            for n, nbrs in nodes_nbrs:
                yield (n, sum((nbrs[nbr].get(weight, 1) for nbr in nbrs)) +
                       (n in nbrs and nbrs[n].get(weight, 1)), nbrs)

    def hyper_degree_iter(self, nbunch=None):
        nodes_nbrs = ((n, self.__hg.incident_edges(n)) for n in self.nbunch_iter(nbunch))

        for n, nbrs in nodes_nbrs:
            yield (n, len(nbrs), nbrs)  # return tuple (n,degree)

    def clear(self):
        """Remove all nodes and edges from the graph.

        This also removes the name, and all graph, node, and edge attributes.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.clear()
        >>> G.nodes()
        []
        >>> G.edges()
        []

        """
        self.__hg.clear()

    def copy(self):
        """Return a copy of the graph.

        Returns
        -------
        G : Graph
            A copy of the graph.

        See Also
        --------
        to_directed: return a directed copy of the graph.

        Notes
        -----
        This makes a complete copy of the graph including all of the
        node or edge attributes.

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> H = G.copy()

        """
        # raise NotImplementedError()
        return copy.deepcopy(self)

    def is_multigraph(self):
        """Return True if graph is a multigraph, False otherwise."""
        return False

    def is_directed(self):
        """Return True if graph is directed, False otherwise."""
        return False

    def to_directed(self):
        """Return a directed representation of the graph.

        Returns
        -------
        G : DiGraph
            A directed graph with the same name, same nodes, and with
            each edge (u,v,data) replaced by two directed edges
            (u,v,data) and (v,u,data).

        Notes
        -----
        This returns a "deepcopy" of the edge, node, and
        graph attributes which attempts to completely copy
        all of the data and references.

        This is in contrast to the similar D=DiGraph(G) which returns a
        shallow copy of the data.

        See the Python copy module for more information on shallow
        and deep copies, http://docs.python.org/library/copy.html.

        Warning: If you have subclassed Graph to use dict-like objects in the
        data structure, those changes do not transfer to the DiGraph
        created by this method.

        Examples
        --------
        >>> G = nx.Graph()   # or MultiGraph, etc
        >>> G.add_path([0,1])
        >>> H = G.to_directed()
        >>> H.edges()
        [(0, 1), (1, 0)]

        If already directed, return a (deep) copy

        >>> G = nx.DiGraph()   # or MultiDiGraph, etc
        >>> G.add_path([0,1])
        >>> H = G.to_directed()
        >>> H.edges()
        [(0, 1)]
        """
        return self.copy()  # copy.deepcopy(self)
        # raise NotImplementedError()

    def to_undirected(self):
        """Return an undirected copy of the graph.

        Returns
        -------
        G : Graph/MultiGraph
            A deepcopy of the graph.

        See Also
        --------
        copy, add_edge, add_edges_from

        Notes
        -----
        This returns a "deepcopy" of the edge, node, and
        graph attributes which attempts to completely copy
        all of the data and references.

        This is in contrast to the similar G=DiGraph(D) which returns a
        shallow copy of the data.

        See the Python copy module for more information on shallow
        and deep copies, http://docs.python.org/library/copy.html.

        Examples
        --------
        >>> G = nx.Graph()   # or MultiGraph, etc
        >>> G.add_path([0,1])
        >>> H = G.to_directed()
        >>> H.edges()
        [(0, 1), (1, 0)]
        >>> G2 = H.to_undirected()
        >>> G2.edges()
        [(0, 1)]
        """
        # return NotImplementedError()
        return deepcopy(self)

    def subgraph(self, nbunch):
        """Return the subgraph induced on nodes in nbunch.

        The induced subgraph of the graph contains the nodes in nbunch
        and the edges between those nodes.

        Parameters
        ----------
        nbunch : list, iterable
            A container of nodes which will be iterated through once.

        Returns
        -------
        G : Graph
            A subgraph of the graph with the same edge attributes.

        Notes
        -----
        The graph, edge or node attributes just point to the original graph.
        So changes to the node or edge structure will not be reflected in
        the original graph while changes to the attributes will.

        To create a subgraph with its own copy of the edge/node attributes use:
        nx.Graph(G.subgraph(nbunch))

        If edge attributes are containers, a deep copy can be obtained using:
        G.subgraph(nbunch).copy()

        For an inplace reduction of a graph to a subgraph you can remove nodes:
        G.remove_nodes_from([ n in G if n not in set(nbunch)])

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> H = G.subgraph([0,1,2])
        >>> H.edges()
        [(0, 1), (1, 2)]
        """
        raise NotImplementedError()

    def nodes_with_selfloops(self):
        return []

    def selfloop_edges(self, data=False, default=None):
        return []

    def number_of_selfloops(self):
        return 0

    def size(self, weight=None):
        """Return the number of edges.

        Parameters
        ----------
        weight : string or None, optional (default=None)
           The edge attribute that holds the numerical value used
           as a weight.  If None, then each edge has weight 1.

        Returns
        -------
        nedges : int
            The number of edges or sum of edge weights in the graph.

        See Also
        --------
        number_of_edges

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.size()
        3

        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_edge('a','b',weight=2)
        >>> G.add_edge('b','c',weight=4)
        >>> G.size()
        2
        >>> G.size(weight='weight')
        6.0
        """
        s = sum(self.degree(weight=weight).values()) / 2
        if weight is None:
            return int(s)
        else:
            return float(s)

    def iter_twin_vertices(self):
        for v in self.__hg.iter_twin_neighbours():
            yield v

    def number_of_edges(self, u=None, v=None):
        """Return the number of edges between two nodes.

        Parameters
        ----------
        u, v : nodes, optional (default=all edges)
            If u and v are specified, return the number of edges between
            u and v. Otherwise return the total number of all edges.

        Returns
        -------
        nedges : int
            The number of edges in the graph.  If nodes u and v are specified
            return the number of edges between those nodes.

        See Also
        --------
        size

        Examples
        --------
        >>> G = nx.Graph()   # or DiGraph, MultiGraph, MultiDiGraph, etc
        >>> G.add_path([0,1,2,3])
        >>> G.number_of_edges()
        3
        >>> G.number_of_edges(0,1)
        1
        >>> e = (0,1)
        >>> G.number_of_edges(*e)
        1
        """
        if u is None: return int(self.size())
        if v in self.__hg.adjByNode(u):
            return 1
        else:
            return 0

    def nbunch_iter(self, nbunch=None):
        """Return an iterator of nodes contained in nbunch that are
        also in the graph.

        The nodes in nbunch are checked for membership in the graph
        and if not are silently ignored.

        Parameters
        ----------
        nbunch : iterable container, optional (default=all nodes)
            A container of nodes.  The container will be iterated
            through once.

        Returns
        -------
        niter : iterator
            An iterator over nodes in nbunch that are also in the graph.
            If nbunch is None, iterate over all nodes in the graph.

        Raises
        ------
        NetworkXError
            If nbunch is not a node or or sequence of nodes.
            If a node in nbunch is not hashable.

        See Also
        --------
        Graph.__iter__

        Notes
        -----
        When nbunch is an iterator, the returned iterator yields values
        directly from nbunch, becoming exhausted when nbunch is exhausted.

        To test whether nbunch is a single node, one can use
        "if nbunch in self:", even after processing with this routine.

        If nbunch is not a node or a (possibly empty) sequence/iterator
        or None, a NetworkXError is raised.  Also, if any object in
        nbunch is not hashable, a NetworkXError is raised.
        """
        if nbunch is None:  # include all nodes via iterator
            bunch = self.nodes_iter()
        elif nbunch in self:  # if nbunch is a single node
            bunch = iter([nbunch])
        else:  # if nbunch is a sequence of nodes
            def bunch_iter(nlist, adj):
                try:
                    for n in nlist:
                        if n in adj:
                            yield n
                except TypeError as e:
                    message = e.args[0]
                    # capture error for non-sequence/iterator nbunch.
                    if 'iter' in message:
                        raise nx.NetworkXError(
                            "nbunch is not a node or a sequence of nodes.")
                    # capture error for unhashable node.
                    elif 'hashable' in message:
                        raise nx.NetworkXError(
                            "Node %s in the sequence nbunch is not a valid node." % n)
                    else:
                        raise

            bunch = bunch_iter(nbunch, self.nodes())
        return bunch
