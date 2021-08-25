__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


from itertools import combinations
import time

import numpy as np
import z3


def at_least_one(bool_vars):
    return z3.Or(bool_vars)

def at_most_one(bool_vars):
    return [z3.Not(z3.And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def sat(data, timeout, rotation):
    
    chip_w = data['chip_w']
    n = data['n']
    inst_x =  data['inst_x']
    inst_y = data['inst_y']
    min_h = data['min_h']
    max_h = data['max_h']
    min_index = data['min_index']

    opt = z3.Optimize()
    opt.set("timeout", timeout*1000)
    
    chip_h = z3.Int("chip_h")
    
    chip = np.empty((chip_w,max_h,n),dtype=z3.BoolRef)
    corners = np.empty((chip_w,max_h,n),dtype=z3.BoolRef)

    if rotation == True:
        rotated = z3.BoolVector("rotated", n)
        new_inst_x = [z3.If(rotated[k], inst_y[k], inst_x[k]) for k in range(n)]
        new_inst_y = [z3.If(rotated[k], inst_x[k], inst_y[k]) for k in range(n)]
    else:
        new_inst_x = inst_x
        new_inst_y = inst_y


    symmetry_breaking = []
    for i in range(chip_w):
        for j in range(max_h):
            temp_chip = []
            temp_corners = []
            for k in range(n):
                chip[i][j][k] = z3.Bool("chip_"+str(i)+"_"+str(j)+"_"+str(k))
                corners[i][j][k] = z3.Bool("corners_"+str(i)+"_"+str(j)+"_"+str(k))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),chip[i][j][k]))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),z3.And(i<=chip_w-new_inst_x[k],j<=max_h-new_inst_y[k])))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),chip_h>=j + new_inst_y[k]))
                temp_chip.append(chip[i][j][k])
                temp_corners.append(corners[i][j][k])
            opt.add(at_most_one(temp_chip))
            opt.add(at_most_one(temp_corners))
            symmetry_breaking.append(z3.And(z3.And(2*i + new_inst_x[min_index] <= chip_w, 2*j + new_inst_y[min_index] <= min_h), corners[i][j][min_index]))

    opt.add(z3.Or(symmetry_breaking))

    for k in range(n):
        temp_corners = []
        for i in range(chip_w):
            for j in range(max_h):
                temp_normal = []
                temp_rotated = []
                for ii in range(chip_w):
                    for jj in range(max_h):
                        if rotation == False:
                            if (ii in range(i,i+inst_x[k]) and jj in range(j,j+inst_y[k])):
                                temp_normal.append(chip[ii][jj][k])
                            else:
                                temp_normal.append(z3.Not(chip[ii][jj][k]))    
                        else:                            
                            if (ii in range(i,i+inst_x[k]) and jj in range(j,j+inst_y[k])):
                                temp_normal.append(z3.Implies(z3.Not(rotated[k]),chip[ii][jj][k]))
                            else:
                                temp_normal.append(z3.Implies(z3.Not(rotated[k]),z3.Not(chip[ii][jj][k])))
                            if (ii in range(i,i+inst_y[k]) and jj in range(j,j+inst_x[k])):
                                temp_rotated.append(z3.Implies(rotated[k],chip[ii][jj][k]))
                            else:
                                temp_rotated.append(z3.Implies(rotated[k],z3.Not(chip[ii][jj][k])))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),z3.And(temp_normal)))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),z3.And(temp_rotated)))
                temp_corners.append(corners[i][j][k])
        opt.add(at_least_one(temp_corners))
        opt.add(at_most_one(temp_corners))

    opt.minimize(chip_h)
    
    start = time.time()
    check = opt.check()
    end = time.time()
    model=opt.model()
    # if rotation == True:
    #     print(str(model.evaluate(rotated[0])))
    result_x=[]
    result_y=[]
    result_inst_x=[]
    result_inst_y=[]
    if check == z3.sat:
        for k in range(n):
            for i in range(chip_w):
                for j in range(int(str(model.evaluate(chip_h)))):
                    if model.evaluate(corners[i][j][k]) == True:
                        result_x.append(i)
                        result_y.append(j)
                        result_inst_x.append(int(str(model.evaluate(new_inst_x[k]))) if rotation == True else new_inst_x[k])
                        result_inst_y.append(int(str(model.evaluate(new_inst_y[k]))) if rotation == True else new_inst_y[k])
        chip_h_int = int(str(model.evaluate(chip_h)))
    else:
        chip_h_int = None
           
    return chip_h_int, result_x, result_y,result_inst_x, result_inst_y, end-start