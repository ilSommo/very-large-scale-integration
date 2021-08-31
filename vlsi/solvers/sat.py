__version__ = '1.0.3'
__author__ = 'Giacomo Berselli, Martino Pulici'


from itertools import combinations
import time

import numpy as np
import z3


def at_least_one(bool_vars):
    """Calculates constraints for at least one true variable.

    Parameters
    ----------
    bool_vars : list
        Boolean variables.

    Returns
    -------
    constraints : list
        z3 constraints.
    """
    constraints = [z3.Or(bool_vars)]

    return constraints


def at_most_one(bool_vars):
    """Calculates constraints for at most one true variable.

    Parameters
    ----------
    bool_vars : list
        Boolean variables.

    Returns
    -------
    constraints : list
        z3 constraints.
    """
    constraints = [z3.Not(z3.And(pair[0], pair[1]))
                   for pair in combinations(bool_vars, 2)]

    return constraints


def sat(data, timeout, rotation):
    """Solves a SAT problem.

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

    # Chip height
    chip_h = z3.Int('chip_h')

    # 3D boolean matrix of circuits' presence
    chip = np.empty((chip_w, max_h, n), dtype=z3.BoolRef)
    # 3D boolean matrix of circuits' corners
    corners = np.empty((chip_w, max_h, n), dtype=z3.BoolRef)

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

    # List of symmetry breaking constraints
    symmetry_breaking = []
    # Cycle coordinates
    for i in range(chip_w):
        for j in range(max_h):
            # Lists for non-overlapping constraints
            temp_chip = []
            temp_corners = []
            # Cycle circuits
            for k in range(n):
                # Fill chip and corners matrices
                chip[i][j][k] = z3.Bool(
                    'chip_' + str(i) + '_' + str(j) + '_' + str(k))
                corners[i][j][k] = z3.Bool(
                    'corners_' + str(i) + '_' + str(j) + '_' + str(k))
                # Boundaries consistency constraint
                opt.add(
                    z3.Implies(
                        corners[i][j][k],
                        z3.And(
                            i + new_inst_x[k] <= chip_w,
                            j + new_inst_y[k] <= chip_h)))
                # Append non-overlapping constraints
                temp_chip.append(chip[i][j][k])
                temp_corners.append(corners[i][j][k])
            # Add non-overlapping constraints
            opt.add(at_most_one(temp_chip))
            opt.add(at_most_one(temp_corners))
            symmetry_breaking.append(
                z3.And(corners[i][j][min_index], z3.And(
                    2 * i +
                    new_inst_x[min_index] <= chip_w,
                    2 * j +
                    new_inst_y[min_index] <= chip_h)))
    # Add symmetry breaking constraints
    opt.add(z3.Or(symmetry_breaking))

    # Cycle circuits
    for k in range(n):
        # List of structural constraints
        temp_corners = []
        # Cycle coordinates
        for i in range(chip_w):
            for j in range(max_h):
                # Lists of structural constraints
                temp_normal = []
                temp_rotated = []
                # Cycle coordinates
                for ii in range(chip_w):
                    for jj in range(max_h):
                        # Enter if rotation is enabled
                        if rotation:
                            # Enter if position is part of non-rotated chip
                            if (ii in range(i,
                                            i + inst_x[k]) and jj in range(j,
                                                                           j + inst_y[k])):
                                # Append structural constraint
                                temp_normal.append(
                                    z3.Implies(
                                        z3.Not(
                                            rotated[k]),
                                        chip[ii][jj][k]))
                            else:
                                # Append structural constraint
                                temp_normal.append(
                                    z3.Implies(
                                        z3.Not(
                                            rotated[k]), z3.Not(
                                            chip[ii][jj][k])))
                            # Enter if position is part of rotated chip
                            if (ii in range(i,
                                            i + inst_y[k]) and jj in range(j,
                                                                           j + inst_x[k])):
                                # Append structural constraint
                                temp_rotated.append(z3.Implies(
                                    rotated[k], chip[ii][jj][k]))
                            else:
                                # Append structural constraint
                                temp_rotated.append(
                                    z3.Implies(
                                        rotated[k], z3.Not(
                                            chip[ii][jj][k])))
                        else:
                            # Enter if position is part of chip
                            if (ii in range(i,
                                            i + inst_x[k]) and jj in range(j,
                                                                           j + inst_y[k])):
                                # Append structural constraint
                                temp_normal.append(chip[ii][jj][k])
                            else:
                                # Append structural constraint
                                temp_normal.append(z3.Not(chip[ii][jj][k]))
                # Add structural constraints
                opt.add(z3.Implies(corners[i][j][k], z3.And(temp_normal)))
                opt.add(z3.Implies(corners[i][j][k], z3.And(temp_rotated)))
                temp_corners.append(corners[i][j][k])
        # Add structural constraints
        opt.add(at_least_one(temp_corners))
        opt.add(at_most_one(temp_corners))

    # Minimize chip height
    opt.minimize(chip_h)

    # Start timer
    start = time.time()
    # Check SAT
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
        # Cycle chips and coordinates
        for k in range(n):
            for i in range(chip_w):
                for j in range(int(str(model.evaluate(chip_h)))):
                    # Enter is corner is present
                    if model.evaluate(corners[i][j][k]):
                        # Append results
                        result_x.append(i)
                        result_y.append(j)
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
