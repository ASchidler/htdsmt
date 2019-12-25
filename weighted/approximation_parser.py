import os
import re
import sys

pth = sys.argv[1]
outp = sys.argv[2]
benchmarks = ["W1", "W1BB", "W2", "W2BB"]
results = {x:  (0, 0, 0) for x in benchmarks}

with open(outp, "w") as output:
    # Write header
    output.write("instance")
    for name in benchmarks:
        output.write(f";{name} weight;{name} time")
    output.write(os.linesep)

    # Go through all results
    for r, d, f in os.walk(pth):
        for file in f:
            # Only out files contain results
            if not file.endswith(".out"):
                continue
            f_result = {}

            with open(os.path.join(r, file)) as c_file:
                content = c_file.readlines()

                # Each line is the result of a different benchmark
                for line in content:
                    # Find matching benchmark in results
                    m = re.match(f"Heuristisc WGHTW([0-9]): BB: (True|False) ([0-9]+) in (.*)$", line)
                    fgroup = int(m.group(1))
                    fbb = True if m.group(2) == "True" else False
                    fweight = int(m.group(3))
                    ftm = float(m.group(3))

                    name = f"W{fgroup}"
                    if fbb:
                        name += "BB"

                    # Set resi;ts
                    f_result[name] = (fweight, ftm)
                    cnt, weight, time = results[name]
                    results[name] = (cnt + 1, weight + fweight, time + ftm)

                # Write results to output
                output.write(file[0:len(file)-4])
                for name in benchmarks:
                    if name in f_result:
                        weight, tm = f_result[name]
                        output.write(f";{weight};{tm}")
                    else:
                        output.write(";;")

    # Output aggregated results
    for name, (cnt, weight, time) in results.items():
        if cnt == 0:
            print(f"{name}\tsolved: 0\twidth: NA\tweight: NA\ttime: NA")
        else:
            print(f"{name}\tsolved: {cnt}\tweight: {weight * 1.0 / cnt}\ttime: {time / cnt}")
