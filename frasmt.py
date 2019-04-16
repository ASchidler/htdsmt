from __future__ import absolute_import

import sys
import select
import inspect
from decimal import Decimal
import frasmt_solver
import os
import subprocess
import solver_decoder
import logging

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from htd_validate import Hypergraph

# End of imports
# Encode solver as string
#solver_decoder.SolverDecoder.encode_z3()

# Disable logging, otherwise PACE runs fail...
logging.disable(logging.FATAL)

# Load graph from input
if not select.select([sys.stdin, ], [], [], 0.0)[0]:
    if len(sys.argv) == 2:
        hypergraph = Hypergraph.from_file(sys.argv[1], fischl_format=False)
    else:
        print "Please provide the input via STDIN or as a filename as the first and only argument"
        exit(1)
else:
    hypergraph = Hypergraph.fromstream_dimacslike(sys.stdin)

# Load solver and check permissions
slv = solver_decoder.SolverDecoder.decode()

# Parameters
epsilon = Decimal(0.001)
is_z3 = True

# Launch SMT solver
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '..'))

encf = open("/tmp/test.txt", "w+")
# Create and pass on the smt encoding
enc = frasmt_solver.FraSmtSolver(hypergraph, stream=encf, checker_epsilon=epsilon)
enc.solve()
encf.close()

encf = open("/tmp/test.txt", "r")
res = open("/tmp/test2.txt", "w+")
if is_z3:
    p1 = subprocess.Popen([slv, '-smt2', '-in'], stdin=encf, stdout=res)
else:
    p1 = subprocess.Popen(slv, stdin=encf, stdout=res)

p1.wait()
res.close()
res = open("/tmp/test2.txt", "r")
outp = res.read()
res.close()

# send eof and wait for output
#outp, err = p1.communicate("")

# Load the resulting model
res = enc.decode(outp, is_z3)

# Display the HTD
td = res['decomposition']
num_edges = len(td.T.edges)

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