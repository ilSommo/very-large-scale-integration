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

def sat(chip_w, n, inst_x, inst_y, max_h, timeout):
    
    opt = z3.Optimize()
    opt.set("timeout", timeout*1000)
    
    chip_h = z3.Int("chip_h")
    
    chip = np.empty((chip_w,max_h,n),dtype=z3.BoolRef)
    corners = np.empty((chip_w,max_h,n),dtype=z3.BoolRef)

    for i in range(chip_w):
        for j in range(max_h):
            temp_chip = []
            temp_corners = []
            for k in range(n):
                chip[i][j][k] = z3.Bool("chip_"+str(i)+"_"+str(j)+"_"+str(k))
                corners[i][j][k] = z3.Bool("corners_"+str(i)+"_"+str(j)+"_"+str(k))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),chip[i][j][k]))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),z3.And(i<=chip_w-inst_x[k],j<=max_h-inst_y[k])))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),chip_h>=j + inst_y[k]))
                temp_chip.append(chip[i][j][k])
                temp_corners.append(corners[i][j][k])
            opt.add(at_most_one(temp_chip))
            opt.add(at_most_one(temp_corners))

    for k in range(n):
        temp_corners = []
        for i in range(chip_w-inst_x[k]+1):
            for j in range(max_h-inst_y[k]+1):
                temp = []
                for ii in range(chip_w):
                    for jj in range(max_h):
                        if (ii in range(i,i+inst_x[k]) and jj in range(j,j+inst_y[k])):
                            temp.append(chip[ii][jj][k])
                        else:
                            temp.append(z3.Not(chip[ii][jj][k]))
                opt.add(z3.Or(z3.Not(corners[i][j][k]),z3.And(temp)))
                temp_corners.append(corners[i][j][k])
        opt.add(at_least_one(temp_corners))
        opt.add(at_most_one(temp_corners))
 
    opt.minimize(chip_h)
    
    start = time.time()
    opt.check()
    end = time.time()
    model=opt.model()
    result_x=[]
    result_y=[]
    try:
        for k in range(n):
            for i in range(chip_w):
                for j in range(int(str(model.evaluate(chip_h)))):
                    if model.evaluate(corners[i][j][k]) == True:
                        result_x.append(i)
                        result_y.append(j)
        chip_h_int = int(str(model.evaluate(chip_h)))
    except:
        chip_h_int = 0
           
    return chip_h_int, result_x, result_y, end-start