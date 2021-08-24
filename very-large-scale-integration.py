__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import datetime
import colorsys

from matplotlib.patches import Rectangle
import matplotlib.pyplot as plt
from minizinc import Instance, Model, Solver
import numpy as np

from vlsi.sat import *
from vlsi.smt import *


NORMAL = True
ROTATION = True

TIMEOUT_CP = 10
TIMEOUT_SAT = 10
TIMEOUT_SMT = 10

MIN_CP = 1
MAX_CP = 5

MIN_SAT = 1
MAX_SAT = 0

MIN_SMT = 1
MAX_SMT = 5

MIN = min(MIN_CP, MIN_SAT, MIN_SMT)
MAX = max(MAX_CP, MAX_SAT, MAX_SMT)


def plot(file, width, height, blocks):
    _, ax = plt.subplots()
    index = 1
    for w, h, x, y, c in blocks:
        ax.add_patch(Rectangle((x, y), w, h, facecolor=c))
        ax.add_patch(Rectangle((x, y), w, h, fill=None, ls='-', lw=2))
        index += 1
    ax.set_xlim(0, width)
    ax.set_ylim(0, height)
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_xticks(range(width + 1))
    ax.set_yticks(range(height + 1))
    ax.grid(color='black')
    plt.title(str(file))
    plt.savefig("out/out-" + file + ".png")
    plt.close()


times_cp = []
times_sat = []
times_smt = []

if ROTATION:
    model = Model("src/cp_rotation.mzn")
else:
    model = Model("src/cp.mzn")
solver = Solver.lookup("chuffed")

for i in range(MIN, MAX + 1):
    file = str(i)
    with open("ins/ins-" + file + ".txt", 'r') as infile:
        chip_w = int(infile.readline().strip())
        n = int(infile.readline().strip())
        inst_x = []
        inst_y = []
        line = infile.readline()
        while line.strip():
            line_split = (line.strip().split(' '))
            inst_x.append(int(line_split[0]))
            inst_y.append(int(line_split[1]))
            line = infile.readline()

    max_h = 0
    inst = zip(inst_x, inst_y)
    while inst:
        inst = sorted(inst, key=lambda tup: tup[0], reverse=True)
        inst = sorted(inst, key=lambda tup: tup[1], reverse=True)
        chip_cumulative = chip_w
        tiles = 0
        k = 0
        heights = []
        while k < len(inst):
            if inst[k][0] <= chip_cumulative:
                chip_cumulative -= inst[k][0]
                tiles += 1
                heights.append(inst[k][1])
                del inst[k]
            else:
                k += 1
        max_h += max(heights)

    if i in range(MIN_CP, MAX_CP + 1):
        instance = Instance(solver, model)
        instance["chip_w"] = chip_w
        instance["n"] = n
        instance["inst_x"] = inst_x
        instance["inst_y"] = inst_y
        instance["max_h"] = max_h

        result = instance.solve(
            timeout=datetime.timedelta(
                seconds=TIMEOUT_CP),
            optimisation_level=5,
            free_search=True)

        try:
            chip_h_cp = result["objective"]
            bl_x_cp = result["bl_x"]
            bl_y_cp = result["bl_y"]
            if ROTATION:
                new_inst_x_cp = result['new_inst_x']
                new_inst_y_cp = result['new_inst_y']
            if chip_h_cp == chip_w:
                time_cp = result.statistics["time"].total_seconds()
                times_cp.append(time_cp)

                output_cp = str(chip_w) + " " + \
                    str(chip_h_cp) + "\n" + str(n) + "\n"
                if ROTATION:
                    for j in range(n):
                        output_cp += str(new_inst_x_cp[j]) + " " + str(
                            new_inst_y_cp[j]) + " " + str(bl_x_cp[j]) + " " + str(bl_y_cp[j]) + "\n"
                else:
                    for j in range(n):
                        output_cp += str(inst_x[j]) + " " + str(inst_y[j]) + \
                            " " + str(bl_x_cp[j]) + " " + str(bl_y_cp[j]) + "\n"

                with open("out/out-" + file + "-cp.txt", 'w') as outfile:
                    outfile.write(output_cp)

                if ROTATION:
                    plot(file + "-cp",
                         chip_w,
                         chip_h_cp,
                         [(new_inst_x_cp[j],
                           new_inst_y_cp[j],
                             bl_x_cp[j],
                             bl_y_cp[j],
                             tuple(value / 255 for value in colorsys.hsv_to_rgb(j / n,
                                                                                0.75,
                                                                                191))) for j in range(n)])
                else:
                    plot(file + "-cp",
                         chip_w,
                         chip_h_cp,
                         [(inst_x[j],
                           inst_y[j],
                             bl_x_cp[j],
                             bl_y_cp[j],
                             tuple(value / 255 for value in colorsys.hsv_to_rgb(j / n,
                                                                                0.75,
                                                                                191))) for j in range(n)])
                print("DONE CP " + str(i) + ": " + str(time_cp) + " s")
            else:
                time_cp = 0
                times_cp.append(time_cp)
                print("FAIL CP " + str(i))
        except BaseException:
            time_cp = 0
            times_cp.append(time_cp)
            print("FAIL CP " + str(i))
    else:
        times_cp.append(0)

    if i in range(MIN_SAT, MAX_SAT + 1):
        chip_h_sat, bl_x_sat, bl_y_sat, time_sat = sat(
            chip_w, n, inst_x, inst_y, max_h, TIMEOUT_SAT)
        if chip_h_sat == chip_w:
            times_sat.append(time_sat)
            output_sat = str(chip_w) + " " + \
                str(chip_h_sat) + "\n" + str(n) + "\n"
            for j in range(n):
                output_sat += str(inst_x[j]) + " " + str(inst_y[j]) + \
                    " " + str(bl_x_sat[j]) + " " + str(bl_y_sat[j]) + "\n"

            with open("out/out-" + file + "-sat.txt", 'w') as outfile:
                outfile.write(output_sat)

            plot(file + "-sat",
                 chip_w,
                 chip_h_sat,
                 [(inst_x[j],
                   inst_y[j],
                     bl_x_sat[j],
                     bl_y_sat[j],
                     tuple(value / 255 for value in colorsys.hsv_to_rgb(j / n,
                                                                        0.75,
                                                                        191))) for j in range(n)])
            print("DONE SAT " + str(i) + ": " + str(time_sat) + " s")
        else:
            time_sat = 0
            times_sat.append(time_sat)
            print("FAIL SAT " + str(i))
    else:
        times_sat.append(0)

    if i in range(MIN_SMT, MAX_SMT + 1):
        chip_h_smt, bl_x_smt, bl_y_smt, time_smt = smt(
            chip_w, n, inst_x, inst_y, max_h, TIMEOUT_SMT)
        if chip_h_smt == chip_w:
            times_smt.append(time_smt)
            output_smt = str(chip_w) + " " + \
                str(chip_h_smt) + "\n" + str(n) + "\n"
            for j in range(n):
                output_smt += str(inst_x[j]) + " " + str(inst_y[j]) + \
                    " " + str(bl_x_smt[j]) + " " + str(bl_y_smt[j]) + "\n"

            with open("out/out-" + file + "-smt.txt", 'w') as outfile:
                outfile.write(output_smt)

            plot(file + "-smt",
                 chip_w,
                 chip_h_smt,
                 [(inst_x[j],
                   inst_y[j],
                     bl_x_smt[j],
                     bl_y_smt[j],
                     tuple(value / 255 for value in colorsys.hsv_to_rgb(j / n,
                                                                        0.75,
                                                                        191))) for j in range(n)])
            print("DONE SMT " + str(i) + ": " + str(time_smt) + " s")
        else:
            time_smt = 0
            times_smt.append(time_smt)
            print("FAIL SMT " + str(i))
    else:
        times_smt.append(0)

_, ax = plt.subplots(1, 1, figsize=(12.8, 7.2))
ax.set_axisbelow(True)
ax.bar(np.arange(MIN, MAX + 1) - 0.15, times_cp, 0.15, label="cp")
ax.bar(np.arange(MIN, MAX + 1), times_sat, 0.15, label="sat")
ax.bar(np.arange(MIN, MAX + 1) + 0.15, times_smt, 0.15, label="smt")
ax.grid(axis='y', which='both')
ax.set_xticks(range(MIN, MAX + 1))
ax.set_xlabel("instance")
ax.set_ylabel("seconds")
plt.yscale('log')
ax.set_ylim(top=max(TIMEOUT_CP, TIMEOUT_SAT, TIMEOUT_SMT))
plt.tick_params(axis='y', which='both')
plt.legend(loc='best')
plt.title("Times")
plt.savefig("out/times.png")
plt.close()
