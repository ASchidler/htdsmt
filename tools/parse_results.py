import os
import json
import tarfile
import sys

input_path = sys.argv[1]


class InstanceResult:
    def __init__(self):
        self.name = None
        self.runtime = 0
        self.memory = 0
        self.result = None


def parse_file(f):
    result = InstanceResult()
    for cln in f:
        cln = cln.decode('ascii')
        if cln.startswith("Real real_time"):
            ct = float(cln.split(":")[1].strip().split(" ")[0].strip())
            if ct < result.runtime:
                print("Fishy")
            result.runtime = max(result.runtime, ct)
        elif cln.startswith("[startup+"):
            ct = float(cln.split("+")[1].split(" ")[0])
            result.runtime = max(result.runtime, ct)
        elif cln.startswith("Current children cumulated memory:") or cln.startswith("Max. memory"):
            cm = float(cln.split(":")[1].strip().split(" ")[0].strip())
            result.memory = max(result.memory, cm)
        elif cln.startswith("{"):
            detk = json.loads(cln)
            result.result = detk['objective']
        elif cln.startswith("Width : "):
            result.result = int(cln.split(":")[1].strip())
        elif cln.startswith("Result:"):
            result.result = int(cln.split(":")[1].split()[0].strip())
        elif cln.startswith("command line"):
            result.name = os.path.split(cln.strip().split(" ")[-1])[-1]

    return result

overall_results = {}
seen_instances = set()


for cff in sorted(os.listdir(input_path)):
    cf = os.path.join(input_path, cff)
    if os.path.isfile(cf):
        if cf.endswith("tar.bz2"):
            results = {}
            overall_results[cf[:-len("tar.bz2")]] = results
            total = 0
            with tarfile.open(cf) as tar_file:
                for ctf in tar_file:
                    cetf = tar_file.extractfile(ctf)
                    cr = parse_file(cetf)
                    # Convert to MB
                    cr.memory /= 1024
                    if cr.result is not None:
                        total += 1
                    if cr.name is not None and len(cr.name) > 2 and cr.name != "sat_runner" and cr.name != "smt_runner":  # ignore flags
                        seen_instances.add(cr.name)
                        if cr.name in results:
                            print(f"Duplicate in {cf}/{ctf}")
                        else:
                            results[cr.name] = cr
                print(f"{cf}: {total}")
        else:
            print(f"Unknown type {cf}")

    print("Done")

seen_instances = sorted(seen_instances)
seen_files = sorted(overall_results.keys())
with open("results.csv", "w") as csvf:
    # Header 1
    for csf in seen_files:
        csvf.write(f";{csf};;")
    csvf.write(os.linesep)

    # Header 2:
    csvf.write("Name")
    for csf in seen_files:
        csvf.write(f";Time;Mem;Width")
    csvf.write(os.linesep)

    for ci in seen_instances:
        csvf.write(ci)
        known_result = None
        for csf in seen_files:
            if ci not in overall_results[csf]:
                csvf.write(";;;")
                continue

            cr = overall_results[csf][ci]
            csvf.write(";%.2f" % cr.runtime)
            csvf.write(";%.2f" % cr.memory)
            csvf.write(";")
            if cr.result is not None:
                csvf.write(f"{cr.result}")
                if known_result is None:
                    known_result = cr.result
                elif known_result != cr.result:
                    print(f"Result disparity for instance {ci} at file {csf}")

        csvf.write(os.linesep)
