__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


import datetime

from minizinc import Instance, Status

from .plots import *
from vlsi.solvers.sat import *
from vlsi.solvers.smt import *


def output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y):
    """Write output.

    Parameters
    ----------
    file : str
        File name.
    chip_w : int
        Chip width.
    chip_h : int
        Chip height.
    n : int
        Number of blocks.
    inst_x : list
        Blocks' widths.
    inst_y : list
        Blocks' heights.
    bl_x : list
        Blocks' horizontal positions.
    bl_y : list
        Blocks' vertical positions.
    """
    # Output string
    output = str(chip_w) + " " + str(chip_h) + "\n" + str(n) + "\n"
    # Cycle for blocks
    for k in range(n):
        # Update output
        output += str(inst_x[k]) + " " + str(inst_y[k]) + " " + str(bl_x[k]) + " " + str(bl_y[k]) + "\n"
    # Open output file
    with open("out/out-"+file+".txt", 'w') as outfile:
        # Write output on output file
        outfile.write(output)

def cp_wrapper(file, data, solver, model, timeout, rotation):
    """Calls the CP solver and returns the computation time.

    Parameters
    ----------
    file : string
        File name.
    data : dict
        Data dictionary.
    solver : minizinc.Solver
        Minizinc solver.
    model : minizinc.Model
        Minizinc model.
    timeout : int
        Timeout in seconds.
    rotation : bool
        Flag for rotation

    Returns
    -------
    time : float
        Computation time in seconds.
    """
    # File name
    file = file + "-cp" if rotation == False else file + "-cp-rot"
    # Minizinc instance
    instance = Instance(solver, model)
    # Instance parameters
    chip_w = instance['chip_w'] = data['chip_w']
    n = instance['n'] = data['n']
    inst_x = instance['inst_x'] = data['inst_x']
    inst_y = instance['inst_y'] = data['inst_y']
    instance['min_h'] = data['min_h']
    instance['max_h'] = data['max_h']
    instance['min_index'] = data['min_index']+1
    min_index=data['min_index']

    # Minizinc result
    result = instance.solve(timeout=datetime.timedelta(seconds=timeout),optimisation_level=5,free_search=True)
    # Enter if optimal solution is found
    if result.status is Status.OPTIMAL_SOLUTION:
        # Chip height
        chip_h = result['objective']
        # Blocks' positions
        bl_x = result['bl_x']
        bl_y = result['bl_y']
        # Enter if rotation is enabled
        if rotation:
            # New blocks' widths and heigths
            inst_x = result['new_inst_x']
            inst_y = result['new_inst_y']
        # Computation time
        time = result.statistics['time'].total_seconds()
        # Write output
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        # Save plot
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        # Print completion status
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        # Null time
        time = 0
        # Print failure status
        print("FAIL " + str(file))
    return time

def sat_wrapper(file,data, timeout, rotation):
    """Calls the SAT solver and returns the computation time.

    Parameters
    ----------
    file : string
        File name.
    data : dict
        Data dictionary.
    timeout : int
        Timeout in seconds.
    rotation : bool
        Flag for rotation

    Returns
    -------
    time : float
        Computation time in seconds.
    """
    # File name
    file = file + "-sat" if rotation == False else file + "-sat-rot"
    # Instance parameters
    chip_w = data['chip_w']
    n = data['n']
    inst_x = data['inst_x']
    inst_y = data['inst_y']
    min_index = data['min_index']
    # Call SAT solver
    chip_h, bl_x, bl_y,inst_x, inst_y, time = sat(data, timeout, rotation)
    # Enter if a result is found
    if chip_h:
        # Write output
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        # Save plot
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        # Print completion status
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        # Null time
        time = 0
        # Print failure status
        print("FAIL " + str(file))

    return time

def smt_wrapper(file,data, timeout, rotation):
    """Calls the SMT solver and returns the computation time.

    Parameters
    ----------
    file : string
        File name.
    data : dict
        Data dictionary.
    timeout : int
        Timeout in seconds.
    rotation : bool
        Flag for rotation

    Returns
    -------
    time : float
        Computation time in seconds.
    """
    # File name
    file = file + "-smt" if rotation == False else file + "-smt-rot"
    # Instance parameters
    chip_w = data['chip_w']
    n = data['n']
    min_index = data['min_index']
    # Call SMT solver
    chip_h, bl_x, bl_y, inst_x, inst_y, time = smt(data, timeout, rotation)
    # Enter if a result is found
    if chip_h:
        # Write output
        output(file, chip_w, chip_h, n, inst_x, inst_y, bl_x, bl_y)
        # Save plot
        plot_chip(file, chip_w,chip_h,tuple(zip(inst_x,inst_y,bl_x,bl_y)),min_index)
        # Print completion status
        print("DONE " + str(file) + ": " + str(time) + " s")
    else:
        # Null time
        time = 0
        # Print failure status
        print("FAIL " + str(file))

    return time