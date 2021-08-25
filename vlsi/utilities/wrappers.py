__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import colorsys
import datetime

from minizinc import Instance, Status

from vlsi.utilities.plots import *
from vlsi.solvers.sat import *
from vlsi.solvers.smt import *

def output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y):
    output = str(chip_w) + " " + str(chip_h) + "\n" + str(n) + "\n"
    for k in range(n):
        output += str(inst_x[k]) + " " + str(inst_y[k]) + " " + str(bl_x[k]) + " " + str(bl_y[k]) + "\n"
    with open("out/out-"+file+".txt", 'w') as outfile:
        outfile.write(output)

def cp_wrapper(file, data, solver, model, timeout, rotation):
    file = file + "-cp" if rotation == False else file + "-cp-rot"
    instance = Instance(solver, model)
    chip_w = instance['chip_w'] = data['chip_w']
    n = instance['n'] = data['n']
    inst_x = instance['inst_x'] = data['inst_x']
    inst_y = instance['inst_y'] = data['inst_y']
    instance['min_h'] = data['min_h']
    instance['max_h'] = data['max_h']
    instance['min_index'] = data['min_index']+1
    min_index=data['min_index']

    result = instance.solve(timeout=datetime.timedelta(seconds=timeout),optimisation_level=5,free_search=True)
    if result.status is Status.OPTIMAL_SOLUTION:
        chip_h = result['objective']
        bl_x = result['bl_x']
        bl_y = result['bl_y']
        if rotation:
            inst_x = result['new_inst_x']
            inst_y = result['new_inst_y']
        time = result.statistics['time'].total_seconds()
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        time = 0
        print("FAIL " + str(file))

    return time

def sat_wrapper(file,data, timeout, rotation):
    file = file + "-sat" if rotation == False else file + "-sat-rot"
    chip_w = data['chip_w']
    n = data['n']
    inst_x = data['inst_x']
    inst_y = data['inst_y']
    min_index = data['min_index']
    chip_h, bl_x, bl_y,inst_x, inst_y, time = sat(data, timeout, rotation)
    
    if chip_h:
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        time = 0
        print("FAIL " + str(file))

    return time

def smt_wrapper(file,data, timeout, rotation):
    file = file + "-smt" if rotation == False else file + "-smt-rot"
    chip_w = data['chip_w']
    n = data['n']
    min_index = data['min_index']

    chip_h, bl_x, bl_y, inst_x, inst_y, time = smt(data, timeout, rotation)
    
    if chip_h:
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        time = 0
        print("FAIL " + str(file))

    return time