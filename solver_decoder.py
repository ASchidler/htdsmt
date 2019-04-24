import solver_enc
import binascii
import os


def decode():
    with open('/tmp/smt_solver', 'wb+') as fl:
        fl.write(binascii.unhexlify(solver_enc.file_enc))

    os.chmod('/tmp/smt_solver', 0o777)
    return '/tmp/smt_solver'


def encode_os():
    with open('optimathsat', 'rb') as fl:
        with open("solver_enc.py", "w+") as f:
            content = fl.read()
            conv = binascii.hexlify(content)
            f.write("file_enc = \"{}\"\n".format(conv))


def encode_z3():
    with open('z3', 'rb') as fl:
        with open("solver_enc.py", "w+") as f:
            content = fl.read()
            conv = binascii.hexlify(content)
            f.write("file_enc = \"{}\"\n".format(conv))
