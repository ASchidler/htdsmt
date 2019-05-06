#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017
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
from __future__ import absolute_import

import logging
import time
import gzip
from bz2 import BZ2File
from cStringIO import StringIO
from itertools import imap, izip

from htd_validate.utils import relabelling as relab

try:
    import backports.lzma as xz

    xz = True
except ImportError:
    xz = False

import copy
import mimetypes

try:
    import cplex as cx
except ImportError:
    cx = None

try:
    import z3
except ImportError:
    z3 = None

try:
    import clingo
except:
    clingo = None

import threading
from htd_validate.utils.integer import safe_int


class SymTab:
    def __init__(self, offset=0):
        self.__offset = offset
        self.name2id = {}
        self.id2name = {}

    def clear(self):
        self.name2id.clear()
        self.id2name.clear()

    @property
    def n2id(self):
        return self.name2id

    @property
    def id2n(self):
        return self.id2name

    def __getitem__(self, key):
        try:
            return self.name2id[key]
        except KeyError:
            val = self.__offset + len(self.name2id) + 1
            self.name2id[key] = val
            self.id2name[val] = key
            return val

    def get(self, key):
        return self.__getitem__(key)


class Hypergraph(object):
    __d = {}
    # __edge_type = type(tuple)
    __edge_type = tuple

    ACCURACY = 0.0000001

    def __init__(self, non_numerical=False, vertices=None):
        self.__edges = dict()
        if vertices is None:
            vertices = set()
        self.__vertices = vertices
        self.__non_numerical = non_numerical
        if self.__non_numerical:
            self.__nsymtab = SymTab()
            self.__elabel = {}

    # def edge_rank(self, n):
    #    return map(lambda x: tuple(x, len(x)), self.adjByNode(n))

    def edge_into(self, vertices, globalgraph):
        vertices = set(vertices)
        inters = vertices.intersection(self.__vertices)
        if len(inters) > 0:
            assert (len(inters) == 1)
            return inters, -1
        else:
            for k, v in globalgraph.__edges.iteritems():
                inters = vertices.intersection(v).intersection(self.__vertices)
                if len(inters) >= 2:
                    assert (len(inters) == 2)
                    return inters, k
        return None, -1

    def iter_twin_neighbours(self):
        ngb = {}
        #TODO: fixme here seems to be something off
        for v in self.nodes_iter():
            tp = tuple(sorted(self.adjByNode(v, strict=False).keys()))
            if tp not in ngb:
                ngb[tp] = []
            ngb[tp].append(v)

        for v in ngb.values():
            assert(len(v) >= 1)
            if len(v) >= 2:
                yield v


    def iter_twin_vertices(self):
        #problem: we need to compare vertices by vertices

        def ngbsOfWrt(u, v):
            ngbs = []
            for e in self.incident_edges(u).values():
                vinside = v in e
                ngbs.append(tuple(sorted(vi for vi in e if vinside or (not vinside and vi != u))))
            return tuple(sorted(ngbs))

        for nds in self.iter_twin_neighbours():
            twins = {}
            reprs = {}
            for u in nds:
                for v in nds:
                    if u >= v:
                        continue
                    elif u in reprs and v in reprs and reprs[u] == reprs[v]:
                        continue
                    elif ngbsOfWrt(u, v) == ngbsOfWrt(v, u):
                        #new representative u for both nodes
                        if v in reprs:
                            reprs[u] = reprs[v]
                            twins[reprs[v]].append(u)
                        elif u in reprs:
                            reprs[v] = reprs[u]
                            twins[reprs[u]].append(v)
                        else:
                            reprs[v] = u
                            reprs[u] = u
                            twins[u] = [u, v]
            for v in twins.values():
                yield v

#    def maximize_fhec(self, timeout=10):
#        if z3 is None:
#            raise ImportError()
#        solver = z3.Optimize()
#        solver.set("timeout", timeout)
#        vars = {}
#        edges = {}
#        #rev = {}
#        start = time.clock()
#        m = z3.Int(name="cliquesize")
#
#        for (k, e) in self.__edges.iteritems():
#            edges[k] = z3.Real(name="edge{0}".format(k))
#            solver.add(edges[k] <= 1)
#            solver.add(edges[k] >= 0)
#
#        for v in self.nodes_iter():
#            vars[v] = z3.Int(name="node{0}".format(v))
#            #rev[vars[v]] = v
#            solver.add(vars[v] <= 1)
#            solver.add(vars[v] >= 0)
#            solver.add(z3.Or(vars[v] == 0, z3.Sum([edges[k] for k in self.incident_edges(v)]) >= 1))
#
#        solver.add(z3.Sum([edges[k] for k in self.__edges]) <= n)
#        solver.add(z3.Sum([vars[v] for v in self.nodes_iter()]) >= m)
#        #solver.add(z3.Or([vars[v] == 1 for v in self.nodes_iter()]))
#        adj = self.adj
#        for u in self.nodes_iter():
#            for v in self.nodes_iter():
#                if u < v and u not in adj[v]:
#                    solver.add(z3.Or(vars[u] == 0, vars[v] == 0))
#            if timeout != 0 and time.clock() - start >= timeout:
#                return None
#        r = None
#        try:
#            #print "solving"
#            r = solver.maximize(m)
#            solver.check()
#        except z3.Z3Exception, e:
#            logging.error(e.message)
#        if r is None:
#            return None
#
#        res = solver.lower(r)
#        #assert(str(res) != 'epsilon' and str(res) != 'unsat' and isinstance(res, z3.IntNumRef) and res.as_long() >= 1)
#        if str(res) == 'epsilon' or str(res) == 'unsat':
#            logging.error(res)
#        elif not isinstance(res, z3.IntNumRef):
#            logging.error("not an int")
#        elif res.as_long() < 1:
#            logging.error("clique result < 1")
#        else:
#            cl = [k for (k, v) in vars.iteritems() if solver.model()[v].as_long() == 1]
#            if len(cl) != res.as_long():
#                logging.error("{0} vs. {1}".format(len(cl), res.as_long()))
#                #assert(len(cl) == res.as_long())
#                return None
#            return cl
#        return None
#

    def largest_hyperedge(self):
        maxe = None
        maxc = 0
        for e in self.__edges.values():
            if len(e) > maxc:
                maxc = len(e)
                maxe = e
        return maxe

    def largest_clique(self, timeout=120):
        if z3 is None:
            raise ImportError()
        solver = z3.Optimize()
        solver.set("timeout", timeout)
        vars = {}
        #rev = {}
        start = time.clock()
        m = z3.Int(name="cliquesize")
        for v in self.nodes_iter():
            vars[v] = z3.Int(name="node{0}".format(v))
            #rev[vars[v]] = v
            solver.add(vars[v] <= 1)
            solver.add(vars[v] >= 0)

        solver.add(z3.Sum([vars[v] for v in self.nodes_iter()]) >= m)
        #solver.add(z3.Or([vars[v] == 1 for v in self.nodes_iter()]))
        adj = self.adj
        for u in self.nodes_iter():
            for v in self.nodes_iter():
                if u < v and u not in adj[v]:
                    solver.add(z3.Or(vars[u] == 0, vars[v] == 0))
            if timeout != 0 and time.clock() - start >= timeout:
                return None
        r = None
        try:
            r = solver.maximize(m)
            solver.check()
        except z3.Z3Exception, e:
            logging.error(e.message)
        if r is None:
            return None

        res = solver.lower(r)
        #assert(str(res) != 'epsilon' and str(res) != 'unsat' and isinstance(res, z3.IntNumRef) and res.as_long() >= 1)
        if str(res) == 'epsilon' or str(res) == 'unsat':
            logging.error(res)
        elif not isinstance(res, z3.IntNumRef):
            logging.error("not an int")
        elif res.as_long() < 1:
            logging.error("clique result < 1")
        else:
            cl = [k for (k, v) in vars.iteritems() if solver.model()[v].as_long() == 1]
            if len(cl) != res.as_long():
                logging.error("{0} vs. {1}".format(len(cl), res.as_long()))
                #assert(len(cl) == res.as_long())
                return None
            #print cl
            return cl
        return None

    # --solve-limit=<n>[,<m>] : Stop search after <n> conflicts or <m> restarts
    def largest_clique_asp(self, clingoctl=None, timeout=10, enum=True, usc=True, ground=False, prevent_k_hyperedge=3,
                           solve_limit="umax,umax"):
        if clingo is None:
            raise ImportError()

        def __on_model(asetx):
            return lambda model: __on_model_2(asetx, model)

        def __on_model_2(asetx, model):
            if len(model.cost) == 0:
                return
            # print(model, model.cost, model.optimality_proven)
            asetx[1] |= model.optimality_proven
            opt = abs(model.cost[0])
            if opt >= asetx[0]:
                if opt > asetx[0]:
                    asetx[2] = []
                asetx[0] = opt
                answer_set = [safe_int(x) for x in str(model).translate(None, "u()").split(" ")]
                # might get "fake" duplicates :(, with different model.optimality_proven
                if answer_set not in asetx[2][-1:]:
                    asetx[2].append(answer_set)

        prog = ""

        if clingoctl is None:
            c = clingo.Control()

            if usc:
                c.configuration.solver.opt_strategy = "usc,pmres,disjoint,stratify"
                c.configuration.solver.opt_usc_shrink = "min"
            c.configuration.solve.opt_mode = "optN" if enum else "opt"
            c.configuration.solve.models = 0
            c.configuration.solve.solve_limit = solve_limit

            guess = ""
            pos = 0
            if len(self.__vertices) > 0:
                guess += "{"
                prog += "#maximize {"
                for u in self.__vertices:
                    prog += " 1,u({0}):u({1}){2}".format(u, u, " }.\n" if pos == len(self.__vertices) - 1 else ";")
                    guess += " u({0}){1}".format(u, " }.\n" if pos == len(self.__vertices) - 1 else ";")
                    pos += 1
                prog += "#show u/1.\n"
                prog += guess

            # has to be clique
            if len(self.__edges) > 0:
                if not ground:
                    prog += ":- u(Y1), u(Y2), not a(Y1, Y2), Y1 < Y2.\n"
                    prog += "a(Y1, Y2) :- e(X, Y1), e(X, Y2), Y1 < Y2.\n"
                    for k, e in self.__edges.iteritems():
                        for v in e:
                            prog += "e({0}, {1}).\n".format(k, v)
                else:
                    adj = self.adj
                    for u in self.__vertices:
                        for v in self.__vertices:
                            if u < v and v not in adj[u]:
                                prog += ":- u({0}), u({1}).\n".format(u, v)
        else:
            c = clingoctl

        aset = [0, False, [], c, []]

        if len(self.__edges) == 0 or len(self.__vertices) == 0:
            return aset

        if not ground and len(self.__edges) > 0:
            prog += ":- "
            for i in xrange(0, prevent_k_hyperedge):
                if i > 0:
                    prog += ", Y{0} < Y{1}, ".format(i - 1, i)
                prog += "e(X, Y{0}), u(Y{0})".format(i)
            prog += ".\n"
            # prog += ":- e(X, Y1), e(X, Y2), e(X, Y3), u(Y1), u(Y2), u(Y3), Y1 < Y2, Y2 < Y3."
        else:
            constr = set()
            for e in self.__edges.values():
                if len(e) <= 2 or len(e) < prevent_k_hyperedge:
                    continue
                # prevent 3 elements from the same edge
                sub = range(0, prevent_k_hyperedge)
                while True:  # sub[0] <= len(e) - prevent_k_hyperedge:
                    rule = []
                    pos = 0
                    # print sub, e
                    for v in sub:
                        rule.append(e[v])
                        pos += 1

                    rule = tuple(sorted(rule))
                    if rule not in constr:
                        constr.add(rule)
                        prog += ":- " + ", ".join(("u({0})".format(r) for r in rule)) + ".\n"

                    if sub[0] == len(e) - prevent_k_hyperedge:
                        break

                    # next position
                    for i in xrange(prevent_k_hyperedge - 1, -1, -1):
                        if sub[i] < len(e) + (i - prevent_k_hyperedge):
                            sub[i] += 1
                            for j in xrange(i + 1, prevent_k_hyperedge):
                                sub[j] = sub[i] + (j - i)
                            break

        # print "XX, ", self.__edges, self.__vertices
        # print(prog)
        c.add("prog{0}".format(prevent_k_hyperedge), [], str(prog))

        def solver(c, om):
            c.ground([("prog{0}".format(prevent_k_hyperedge), [])])
            # print "grounded"
            c.solve(on_model=om)

        t = threading.Thread(target=solver, args=(c, __on_model(aset)))
        t.start()
        t.join(timeout)
        c.interrupt()
        t.join()

        aset[1] |= c.statistics["summary"]["models"]["optimal"] > 0
        aset[4] = c.statistics
        # print c.statistics
        return aset

    def relabel_consecutively(self, revert=True):
        return self.relabel(relab.consecutive_substitution(self.__vertices),
                            relab.consecutive_substitution(self.__edges),
                            revert=revert)

    def relabel(self, substitution, substitution_keys, revert=True):
        self.__vertices = relab.relabel_sequence(self.__vertices, substitution)
        self.__edges = relab.relabel_dict(self.__edges, substitution, substitution_keys)
        if not revert:
            return None, None
        return relab.revert_substitution(substitution), relab.revert_substitution(substitution_keys)

    def fractional_cover(self, verts, solution=None, opt=-1, accuracy=ACCURACY):
        if cx is None:
            raise ImportError()

        if solution is None and len(verts) <= 1:
            return 1.0

        problem = cx.Cplex()
        problem.objective.set_sense(problem.objective.sense.minimize)

        names = ["e{0}".format(e) for e in self.edges()]
        # coefficients
        problem.variables.add(obj=[1] * len(self.edges()),
                              lb=[0] * len(self.edges()),
                              # ub=upper_bounds,
                              names=names)

        # constraints
        constraints = []
        for k in verts:
            constraint = []
            for e in self.incident_edges(k):
                constraint.append("e{0}".format(e))
            if len(constraint) > 0:
                constraints.append([constraint, [1] * len(constraint)])

        problem.linear_constraints.add(lin_expr=constraints,
                                       senses=["G"] * len(constraints),
                                       rhs=[1] * len(constraints))  # ,
        # names=["c{0}".format(x) for x in names])
        if opt >= 0:
            problem.linear_constraints.add(lin_expr=[[names, [1] * len(names)]],
                                           senses=["E"], rhs=[opt])

        problem.set_results_stream(None)
        problem.set_error_stream(None)
        problem.set_warning_stream(None)
        problem.set_log_stream(None)
        problem.solve()
        assert (problem.solution.get_status() == 1)

        if solution is not None:
            pos = 0
            for v in problem.solution.get_values():
                if v >= accuracy:
                    solution[int(names[pos][1:])] = v + accuracy
                pos += 1

        return problem.solution.get_objective_value()
        # print problem.solution.get_values()

    # @staticmethod
    # def project_edge(e, p):
    #    return [x for x in e if x not in p]

    def induce_edges(self, es):
        for k, e in es.iteritems():
            self.add_hyperedge([x for x in e if x in self.__vertices], edge_id=k)

    # can also contract edge parts >= 2, e[0] is the part of the edge that is kept
    def contract_edge(self, e, erepr):
        assert (len(e) >= 2)
        assert (erepr in e)
        dl = -1
        excl = None
        for (k, v) in self.__edges.iteritems():
            contr = [x for x in v if x not in e]
            if len(contr) == 0:  # and contr[0] == e[0]:
                dl = k
            elif (len(contr) + 1 < len(v)) or (len(contr) + 1 == len(v) and erepr not in v):
                excl = erepr
                contr.append(erepr)
                if self.isSubsumed(set(contr), modulo=k):
                    dl = k
                else:
                    self.__edges[k] = Hypergraph.__edge_type(contr)
            elif erepr in v:
                excl = erepr
        if dl >= 0:
            del self.__edges[dl]
        self.__vertices.difference_update(e)
        if excl is not None:
            self.__vertices.update((excl,))

    def incident_edges(self, v):
        edges = {}
        for (e, ge) in self.__edges.iteritems():
            if v in ge:
                edges[e] = ge
        return edges

    def edge_rank(self, n):
        # print self.incident_edges(n).values()
        return map(lambda x: (x, len(x)), self.incident_edges(n).values())

    # @staticmethod
    # def project_edge(e, p):
    #    return [x for x in e if x not in p]

    # def inc(self,v):
    #    nbh = dict()
    #    for e in self.__edges.values():
    #        if v in e:
    #            nbh[e] = Hypergraph.__d
    #    return nbh

    def adjByNode(self, v, strict=True):
        nbh = dict()
        for e in self.__edges.values():
            if v in e:
                for ex in e:
                    if not strict or ex != v:
                        nbh[ex] = Hypergraph.__d
        return nbh

    @property
    def adj(self):
        nbhs = dict()
        for k in self.__vertices:
            nbhs[k] = self.adjByNode(k)
        return nbhs

    def __delitem__(self, v):
        # please do not make me copy everything :(
        # assert(Hypergraph.__edge_type == type(list))
        self.__vertices.remove(v)
        # del self.__vertices[v]
        dl = []
        for k, e in self.__edges.iteritems():
            if v in self.__edges[k]:
                # thank you, tuple!
                # del self.__edges[k][v]
                e = set(e)
                e.remove(v)
                self.__edges[k] = Hypergraph.__edge_type(e)
                # print self.__edges[k]
                dl.append((k, e))
        for k, e in dl:
            if len(e) <= 1 or self.isSubsumed(e, modulo=k):
                del self.__edges[k]

    def number_of_edges(self):
        return len(self.__edges)

    def size_largest_hyperedge(self):
        ret = 0
        for i in self.__edges:
            ret = max(ret, len(self.__edges[i]))
        return ret

    def number_of_nodes(self):
        return len(self.__vertices)

    def edges_iter(self):
        return iter(self.__edges.values())

    # bool operator so to say
    def __nonzero__(self):
        return True
        # return len(self.__edges) > 0

    def __copy__(self):
        hg = Hypergraph(non_numerical=self.__non_numerical, vertices=self.__vertices)
        hg.__edges = self.__edges
        if self.__non_numerical:
            hg.__nsymtab = self.__nsymtab
            hg.__elabel = self.__elabel

    def __deepcopy__(self, memodict={}):
        # assert(False)
        hg = Hypergraph(non_numerical=self.__non_numerical, vertices=copy.deepcopy(self.__vertices, memodict))
        hg.__edges = copy.deepcopy(self.__edges, memodict)
        if self.__non_numerical:
            # do not deep copy this stuff, not needed for now
            hg.__nsymtab = self.__nsymtab
            hg.__elabel = self.__elabel
        return hg

    def copy(self):
        return copy.deepcopy(self)

    # TODO: copy?
    # @property
    def nodes(self):
        return self.__vertices

    # TODO: copy?
    # @property
    def edges(self):
        return self.__edges

    def get_edge(self, e):
        return self.__edges[e]

    def edge_ids_iter(self):
        return iter(self.__edges.keys())

    # TODO:
    def nodes_iter(self):
        return iter(self.__vertices)

    @classmethod
    def fromstream_dimacslike(clazz, stream):
        num_edges = 0
        num_verts = 0

        is_dimacs = True
        HG = clazz()
        for line in stream.readlines():
            line = line.split()
            if not line:
                continue
            elif line[0] == 'p':
                is_dimacs = line[1] == 'htd'
            elif line[0] != 'c':
                if is_dimacs:
                    HG.add_hyperedge(map(int, line[1:]))
                else:
                    HG.add_hyperedge(map(int, line))

        if HG.number_of_edges() < num_edges:
            print("edges missing: read=%s announced=%s" % (HG.number_of_edges(), num_edges))
        if HG.number_of_nodes() < num_verts:
            print("vertices missing: read=%s announced=%s" % (HG.number_of_edges(), num_edges))
        return HG

    # TODO: symtab

    @classmethod
    def fromstream_fischlformat(clazz, stream):
        HG = clazz(non_numerical=True)

        for line in stream:
            line = line.replace('\n', '')[:-1]
            edge_name = None
            edge_vertices = []
            #replace whitespaces
            line = line.replace(' ','')

            collect = []
            for char in line:
                if char == '(':
                    edge_name = ''.join(collect)
                    collect = []
                elif char == ',' or char == ')':
                    edge_vertices.append(''.join(collect))
                    collect = []
                elif char != ')':
                    collect.append(char)
            # print(edge_vertices)
            HG.add_hyperedge(edge_vertices, name=edge_name)
        return HG

    # TODO: move from_file to a central part

    @classmethod
    def from_file(clazz, filename, strict=False, fischl_format=False):
        """
        :param filename: name of the file to read from
        :type filename: string
        :rtype: Graph
        :return: a list of edges and number of vertices
        """
        return clazz._from_file(filename, fischl_format=fischl_format)

    # TODO: check whether we need the header_only option
    @classmethod
    def _from_file(clazz, filename, header_only=False, fischl_format=False):
        """
        :param filename: name of the file to read from
        :type filename: string
        :param header_only: read header only
        :rtype: Graph
        :return: imported hypergraph
        """
        if header_only:
            raise NotImplemented
        stream = None
        hypergraph = clazz()
        try:
            mtype = mimetypes.guess_type(filename)[1]
            if mtype is None:
                stream = open(filename, 'r')
            elif mtype == 'bzip2':
                stream = BZ2File(filename, 'r')
            elif mtype == 'gz':
                stream = gzip.open(filename, 'r')
            elif mtype == 'xz' and xz:
                stream = xz.open(filename, 'r')
            else:
                raise IOError('Unknown input type "%s" for file "%s"' % (mtype, filename))
            if fischl_format:
                hypergraph = Hypergraph.fromstream_fischlformat(stream)
            else:
                hypergraph = Hypergraph.fromstream_dimacslike(stream)
        finally:
            if stream:
                stream.close()

        return hypergraph

    def clear(self):
        self.__vertices.clear()
        self.__edges.clear()
        if self.__non_numerical:
            self.__elabel.clear()
            self.__nsymtab.clear()

    def add_node(self, x):
        if self.__non_numerical:
            v = self.__nsymtab[x]
        else:
            v = x
        self.__vertices.add(v)
        return v

    def add_hyperedge(self, X, name=None, edge_id=None):
        # print name
        if len(X) <= 1:
            return
        if self.__non_numerical:
            X = map(self.__nsymtab.get, X)
        # print X
        if edge_id is None:
            edge_id = len(self.__edges) + 1

        if self.__non_numerical and name is not None:
            self.__elabel[edge_id] = name

        # remove/avoid already subsets of edges
        if not self.isSubsumed(set(X), checkSubsumes=True):
            self.__edges[edge_id] = Hypergraph.__edge_type(X)
            self.__vertices.update(X)
        # else:
        #    print("subsumed: ", X)
        return X

    def isSubsumed(self, sx, checkSubsumes=False, modulo=-1):
        for k, e in self.__edges.iteritems():
            if k == modulo:
                continue
            elif sx.issubset(e):
                return True
            elif checkSubsumes and sx.issuperset(e):  # reset the edge
                # print sx, e
                # self.__edges[k][:] = sx
                self.__edges[k] = Hypergraph.__edge_type(sx)
                self.__vertices.update(sx)
                return True
        return False

    def edge_iter(self):
        return self.__edges.iterkeys()

    def __iter__(self):
        return self.edge_iter()

    def __contains__(self, v):
        return v in self.__vertices

    def __len__(self):
        return len(self.__vertices)

    def num_hyperedges(self):
        return len(self.__edges)

    def get_nsymtab(self):
        return self.__nsymtab

    def write_dimacs(self, stream):
        return self.write_graph(stream, dimacs=True)

    def write_gr(self, stream):
        return self.write_graph(stream, dimacs=False)

    def write_graph(self, stream, dimacs=False):
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
        gr_string = 'edge' if dimacs else 'htw'
        s = 'p ' if dimacs else ''
        stream.write('p %s %s %s\n' % (gr_string, self.number_of_nodes(), self.number_of_edges()))
        s = 'e ' if dimacs else ''
        for e_id, nodes in izip(xrange(self.number_of_edges()), self.edges_iter()):
            nodes = ' '.join(imap(str, nodes))
            stream.write('%s%s %s\n' % (s, e_id + 1, nodes))
        stream.flush()

    def __str__(self):
        string = StringIO()
        self.write_gr(string)
        return string.getvalue()

    def __repr__(self):
        return self.__str__()
