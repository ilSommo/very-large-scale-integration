__version__ = '1.0.3'
__author__ = 'Giacomo Berselli, Martino Pulici'


import time

import z3


def smt(data, timeout, rotation):
    """Solves a SMT problem.

    Parameters
    ----------
    data : dict
        Data dictionary.
    timeout : int
        Timeout in seconds.
    rotation : bool
        Flag for rotation.

    Returns
    -------
    chip_h_int : int
        Chip height.
    result_x : int
        Circuits' horizontal positions.
    result_y : int
        Circuits' vertical positions.
    result_inst_x : int
        Circuits' widths.
    result_inst_y : int
        Circuits' heights.
    computation_time : float
        Computation time in seconds.
    """
    # Instance parameters
    chip_w = data['chip_w']
    n = data['n']
    inst_x = data['inst_x']
    inst_y = data['inst_y']
    min_h = data['min_h']
    max_h = data['max_h']
    min_index = data['min_index']

    # Z3 optimizer
    opt = z3.Optimize()
    opt.set('timeout', timeout * 1000)

    # Circuits' positions
    bl_x = z3.IntVector('bl_x', n)
    bl_y = z3.IntVector('bl_y', n)

    # Chip height
    chip_h = z3.Int('chip_h')

    # Add chip height constraints
    opt.add(chip_h >= min_h)
    opt.add(chip_h <= max_h)

    # Enter if rotation is enabled
    if rotation:
        # Boolean vector to flag rotated circuits
        rotated = z3.BoolVector('rotated', n)
        # Actual circuits' widths and heights
        new_inst_x = [z3.If(rotated[k], inst_y[k], inst_x[k])
                      for k in range(n)]
        new_inst_y = [z3.If(rotated[k], inst_x[k], inst_y[k])
                      for k in range(n)]
    else:
        # Actual circuits' widths and heights
        new_inst_x = inst_x
        new_inst_y = inst_y

    # Cycle circuits
    for k in range(n):
        # Add boundaries consistency constraints
        opt.add(bl_x[k] >= 0)
        opt.add(bl_x[k] + new_inst_x[k] <= chip_w)
        opt.add(bl_y[k] >= 0)
        opt.add(bl_y[k] + new_inst_y[k] <= chip_h)
        # Cycle circuits
        for l in range(k + 1, n):
            # Add non-overlapping constraints
            opt.add(
                z3.Or(
                    (bl_x[k] + new_inst_x[k] <= bl_x[l]),
                    (bl_x[k] >= bl_x[l] + new_inst_x[l]),
                    (bl_y[k] + new_inst_y[k] <= bl_y[l]),
                    (bl_y[k] >= bl_y[l] + new_inst_y[l])))

    # Add symmetry breaking constraints
    opt.add(
        z3.And(
            ((2 * bl_x[min_index] + new_inst_x[min_index]) <= chip_w),
            ((2 * bl_y[min_index] + new_inst_y[min_index]) <= chip_h)))

    # Minimize chip height
    opt.minimize(chip_h)
    # Start timer
    start = time.time()
    # Check SMT
    check = opt.check()
    # Stop timer
    end = time.time()
    # Save model
    model = opt.model()
    # Result lists
    result_x = []
    result_y = []
    result_inst_x = []
    result_inst_y = []
    # Enter if optimal solution is found
    if check == z3.sat:
        # Cycle chips
        for k in range(n):
            # Append results
            result_x.append(int(str(model.evaluate(bl_x[k]))))
            result_y.append(int(str(model.evaluate(bl_y[k]))))
            result_inst_x.append(
                int(str(model.evaluate(new_inst_x[k]))) if rotation else new_inst_x[k])
            result_inst_y.append(
                int(str(model.evaluate(new_inst_y[k]))) if rotation else new_inst_y[k])
        # Chip height
        chip_h_int = int(str(model.evaluate(chip_h)))
    else:
        # Chip null height
        chip_h_int = None
    # Computation time
    computation_time = end - start

    return chip_h_int, result_x, result_y, result_inst_x, result_inst_y, computation_time
