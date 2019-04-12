from __future__ import absolute_import

import sys
import select
import inspect
import os
from decimal import Decimal
from cStringIO import StringIO
import logging
import ctypes
import frasmt_solver
import os

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from htd_validate import Hypergraph
from fhtd import FractionalHypertreeDecomposer, utils
from fhtd.utils import sha256_checksum

if not select.select([sys.stdin,],[],[],0.0)[0]:
    if len(sys.argv) == 2:
        hypergraph = Hypergraph.from_file(sys.argv[1], fischl_format=False)
    else:
        print "Please provide the input via STDIN or as the first and only argument"
        exit(1)
else:
    hypergraph = Hypergraph.fromstream_dimacslike(sys.stdin)

epsilon = Decimal(0.001)
stream = StringIO()
stream2 = open("test.txt", "w+")

enc = frasmt_solver.FraSmtSolver(hypergraph, stream=stream2, checker_epsilon=epsilon)
enc.solve()
stream2.close()
is_z3 = False
outp = os.popen('./z3 -smt2 test.txt').read() if is_z3 else os.popen('./optimathsat < test.txt').read()
res = enc.decode(outp, is_z3)

try:
    td = res['decomposition']
    num_edges = len(td.T.edges)
    # set to True for fhtw only
    sys.stdout.write('s htd {} {} {} {}\n'.format(len(td.bags), res['objective'], td.num_vertices, num_edges))

    # Print bag information
    for edge in xrange(1, num_edges+1):
        sys.stdout.write('b {}'.format(edge))

        for vx in td.bags.get(edge):
            sys.stdout.write(' {}'.format(vx))
        sys.stdout.write('\n')

    for v1, v2 in td.T.edges:
        sys.stdout.write('{} {}\n'.format(v1, v2))

    for v1, vals in td.hyperedge_function.iteritems():
        for v2, val in vals.iteritems():
            sys.stdout.write('w {} {} {}\n'. format(v1, v2, val))


    # .update({'width': res['objective'], 'subsolvers': res['subsolvers'], 'solved': 1,
    #                'solver_wall': 0, 'pre_wall': res['pre_wall'], 'enc_wall': res['enc_wall'],
    #                'wall': 0, 'pre_clique_size': res['pre_clique_size'],
    #                'pre_clique_k': res['pre_clique_k'], 'num_twins': res['pre_num_twins'],
    #                'pre_size_max_twin': res['pre_size_max_twin']})
except utils.signals.InterruptException:
    logging.error("Interrupted by signal.")
except ctypes.ArgumentError:
    logging.error("Interrupted by signal.")