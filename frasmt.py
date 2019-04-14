from __future__ import absolute_import

import sys
import select
import inspect
from decimal import Decimal
import frasmt_solver
import os
import subprocess
import binascii
import urllib
import tarfile
import urllib2
import socket
import httplib
import ssl

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from htd_validate import Hypergraph

# End of imports

# slv = open('optimathsat.py', 'r')
# slv_c = open('optimathsat.txt', 'w+')
# str = binascii.b2a_uu(slv.read())
# slv_c.write(str)
# slv_c.close()
# slv.close()

# Load graph from input
if not select.select([sys.stdin, ], [], [], 0.0)[0]:
    if len(sys.argv) == 2:
        hypergraph = Hypergraph.from_file(sys.argv[1], fischl_format=False)
    else:
        print "Please provide the input via STDIN or as a filename as the first and only argument"
        exit(1)
else:
    hypergraph = Hypergraph.fromstream_dimacslike(sys.stdin)


def MyResolver(host):
    if host == 'optimathsat.disi.unitn.it':
        return "193.205.211.30"  # Google IP
    else:
        return host


class MyHTTPConnection(httplib.HTTPConnection):
    def connect(self):
        self.sock = socket.create_connection((MyResolver(self.host), self.port), self.timeout)


class MyHTTPSConnection(httplib.HTTPSConnection):
    def connect(self):
        sock = socket.create_connection((MyResolver(self.host), self.port), self.timeout)
        self.sock = ssl.wrap_socket(sock, self.key_file, self.cert_file)


class MyHTTPHandler(urllib2.HTTPHandler):
    def http_open(self, req):
        return self.do_open(MyHTTPConnection, req)


class MyHTTPSHandler(urllib2.HTTPSHandler):
    def https_open(self, req):
        return self.do_open(MyHTTPSConnection, req)


opener = urllib2.build_opener(MyHTTPHandler, MyHTTPSHandler)
urllib2.install_opener(opener)
filedata = urllib2.urlopen("http://optimathsat.disi.unitn.it/releases/optimathsat-1.6.2/optimathsat-1.6.2-linux-64-bit.tar.gz", "/tmp/optimathsat.tar.gz")

datatowrite = filedata.read()

with open('/tmp/optimathsat.tar.gz', 'wb') as f:
    f.write(datatowrite)


slv = None
tf = tarfile.open("/tmp/optimathsat.tar.gz")
for tfl in tf.getmembers():
    if tfl.name.endswith('bin/optimathsat'):
        tf.extract(tfl, "/tmp")
        slv = os.path.join("/tmp", tfl.name)

# Parameters
epsilon = Decimal(0.001)
is_z3 = False

# Launch SMT solver
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
src_path = os.path.realpath(os.path.join(src_path, '..'))

if is_z3:
    p1 = subprocess.Popen([os.path.join(src_path, 'z3'), '-smt2', '-in'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
else:
    p1 = subprocess.Popen(slv, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

# Create and pass on the smt encoding
enc = frasmt_solver.FraSmtSolver(hypergraph, stream=p1.stdin, checker_epsilon=epsilon)
enc.solve()

# send eof and wait for output
outp, err = p1.communicate("")

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