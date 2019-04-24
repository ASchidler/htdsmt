#!/usr/bin/env false
# -*- coding: utf-8 -*-
#
# Copyright 2017

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
#
from __future__ import print_function

import gzip
import logging

from bz2 import BZ2File
from cStringIO import StringIO
from itertools import count, izip

try:
    import backports.lzma as xz

    xz = True
except ImportError:
    xz = False

import mimetypes
import networkx as nx


def complete_graph(vertices):
    g1 = nx.complete_graph(len(vertices))
    g1 = nx.relabel_nodes(g1, mapping=dict(izip(g1.nodes(), vertices)), copy=True)
    return g1


class Graph(nx.Graph):
    def __init__(self, data=None, val=None, **attr):
        super(Graph, self).__init__(data=data)
        self.val = val

    @classmethod
    def from_file(clazz, filename, strict=False, fischl_format=False):
        """
        :param filename: name of the file to read from
        :type filename: string
        :rtype: Graph
        :return: a list of edges and number of vertices
        """
        return clazz._from_file(filename, strict=strict)

    @staticmethod
    def dimacs_header(filename, strict):
        """
        :param filename: name of the file to read from
        :type filename: string
        :return: a list of edges and number of vertices
        """
        return Graph._from_file(filename, header_only=True, strict=strict)

    @classmethod
    def _parsed_file_line(cls, graph, line):
        pass

    @classmethod
    def _from_file(clazz, filename, header_only=False, strict=False):
        """
        :param filename: name of the file to read from
        :type filename: string
        :param header_only: read header only
        :rtype: Graph
        :return: imported hypergraph
        """
        num_edges = None
        num_verts = None
        is_dimacs = False
        stream = None
        graph = clazz()
        try:
            mtype = mimetypes.guess_type(filename)[1]
            if mtype is None:
                stream = open(filename, 'r')
            elif mtype == 'bzip2':
                stream = BZ2File(filename, 'r')
            elif mtype == 'gz' or mtype == 'gzip':
                stream = gzip.open(filename, 'r')
            elif mtype == 'xz' and xz:
                stream = xz.open(filename, 'r')
            else:
                raise IOError('Unknown input type "%s" for file "%s"' % (mtype, filename))
            nr = 0
            header_seen = False
            for line in stream:
                nr += 1
                line = line.split()
                if line == [] or line[0] in ('x', 'n'):
                    continue
                elif line[0] == 'p':
                    if header_seen:
                        logging.critical('L(%s). Duplicate header. Exiting.' % nr)
                        exit(3)
                    if len(line) > 4:
                        logging.critical('L(%s). Too many arguments. Exiting.' % nr)
                        exit(3)
                    is_dimacs = line[1] == 'edge'
                    is_formula = line[1] == 'cnf'
                    num_verts = int(line[2])
                    num_edges = int(line[3])
                    if header_only:
                        return num_verts, num_edges
                    if num_verts == 0:
                        logging.warning("Empty graph.")
                        return graph
                    header_seen = True
                elif line[0] != 'c' and (is_dimacs or (line[0] != 'a' and line[0] != 'e')): #now also ignores forAll and Exists :P
                    if not header_seen:
                        logging.critical('L(%s). Lines before header. Exiting.' % nr)
                        exit(3)
                    try:
                        if is_dimacs:
                            graph.add_edge(int(line[1]), int(line[2]))
                        elif is_formula:
                            atoms = map(lambda x: abs(int(x)), line[0:-1])
                            #print("formula{0}".format(atoms))
                            for i in atoms:
                                for j in atoms:
                                    if i < j:
                                        graph.add_edge(i, j)    #abs -> then it also works for qbf
                            num_edges += (len(atoms) * (len(atoms) - 1)) / 2 - 1
                        else:
                            graph.add_edge(int(line[0]), int(line[1]))
                        assert(0 not in graph.nodes())
                    except ValueError, e:
                        logging.critical('L(%s). Invalid integer. Exiting.' % nr)
                        logging.critical('Error was: %s' % e)
                        exit(3)
                    except IndexError, e:
                        logging.critical('L(%s). Incomplete edge. Exiting' % nr)
                        logging.critical('Error was: %s' % e)
                        exit(3)
                clazz._parsed_file_line(graph, line)
        finally:
            if stream:
                stream.close()

        if graph.number_of_edges() > num_edges:
            logging.error("Edges overmuch: read=%s expected=%s" % (graph.number_of_edges(), num_edges))
            exit(3)
        if strict and graph.number_of_edges() < num_edges:
            logging.error("Edges missing: read=%s expected=%s" % (graph.number_of_edges(), num_edges))
            exit(3)
        if graph.number_of_nodes() > num_verts:
            logging.error("Vertices overmuch: read=%s expected=%s" % (graph.number_of_nodes(), num_verts))
            #print(graph.nodes())
            exit(3)
        if strict and graph.number_of_nodes() < num_verts:
            logging.error("Vertices missing: read=%s expected=%s" % (graph.number_of_nodes(), num_verts))
            exit(3)
        return graph

    def write_dimacs(self, stream, copy=True):
        return self.write_graph(stream, copy, dimacs=True)

    def write_gr(self, stream, copy=True):
        return self.write_graph(stream, copy, dimacs=False)

    def write_graph(self, stream, copy=True, dimacs=False):
        """
        :param stream: stream where to output the hypergraph
        :type stream: cString
        :param copy: return a copy of the original hypergraph
        :type copy: bool
        :param dimacs: write dimacs header (or gr header)
        :type dimacs: bool
        :rtype Graph, dict
        :return: written hypergraph, remapping of vertices from old hypergraph
        """
        mapping = {org_id: id for id, org_id in izip(count(start=1), self.nodes_iter())}
        graph = nx.relabel_nodes(self, mapping, copy=copy)
        gr_string = 'edge' if dimacs else 'tw'
        s = 'p ' if dimacs else ''
        stream.write('p %s %s %s\n' % (gr_string, graph.number_of_nodes(), graph.number_of_edges()))
        for u, v in graph.edges_iter():
            stream.write('%s%s %s\n' % (s, u, v))
        stream.flush()
        return graph, mapping

    def __str__(self):
        string = StringIO()
        self.write_gr(string)
        return string.getvalue()
