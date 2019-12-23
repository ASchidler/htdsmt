import os
import re
import sys

pth = sys.argv[1]
outp = sys.argv[2]
benchmarks = ["GHTW1", "WGHTW1", "GHTW2", "WGHTW2"]
results = {x:  (0, 0, 0, 0) for x in benchmarks}

with open(outp, "w") as output:
    # Write header
    output.write("instance;")
    for name in benchmarks:
        output.write(f";{name} width;{name} weight;{name} time")
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
                    for name, (cnt, width, weight, time) in results.items():
                        if line.strip().startswith(name):
                            # {arse
                            m = re.match(f"{name}: ([0-9]+) - width: ([0-9]+) in (.*)$", line)
                            fweight = int(m.group(1))
                            fwidth = int(m.group(2))
                            ftm = float(m.group(3))
                            # Set resi;ts
                            f_result[name] = (fwidth, fweight, ftm)
                            results[name] = (cnt + 1, width + fwidth, weight + fweight, time + ftm)
                            break

                # Write results to output
                output.write(file[0:len(file)-4])
                for name in benchmarks:
                    if name in f_result:
                        width, weight, tm = f_result[name]
                        output.write(f";{width};{weight};{tm}")
                    else:
                        output.write(";;;")
                output.write(os.linesep)

    # Output aggregated results
    for name, (cnt, width, weight, time) in results.items():
        if cnt == 0:
            print(f"{name}\tsolved: 0\twidth: NA\tweight: NA\ttime: NA")
        else:
            print(f"{name}\tsolved: {cnt}\twidth: {width * 1.0 / cnt}\tweight: {weight * 1.0 / cnt}\ttime: {time / cnt}")
