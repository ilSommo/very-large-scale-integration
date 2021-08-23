import z3
import time

def sat(chip_w, n, inst_x, inst_y):
    
    opt = z3.Optimize()
    opt.set("timeout", 10000)

    max_h = sum(inst_y)

    corners_w = chip_w
    corners_h = max_h
    # print(corners_w,corners_h)
    # chip_s = chip_w * max_h * n
    # corners_s = corners_w * corners_h * n

    chip = []
    corners = []

    for i in range(chip_w):
        col = []
        for j in range(max_h):
            col.append(z3.BoolVector('chip_'+str(i)+'_'+str(j), n))
        chip.append(col)

    for i in range(corners_w):
        col = []
        for j in range(corners_h):
            col.append(z3.BoolVector('corners_'+str(i)+'_'+str(j), n))
        corners.append(col)


    for i in range(chip_w):
        for j in range(max_h):
            opt.add(z3.Sum([z3.If(chip[i][j][k],1,0) for k in range(n)])<=1)

    for i in range(corners_w):
        for j in range(corners_h):
            opt.add(z3.Sum([z3.If(corners[i][j][k],1,0) for k in range(n)])<=1)

    for k in range(n):
        opt.add([z3.Or(z3.Not(corners[i][j][k]),chip[i][j][k]) for j in range(corners_h) for i in range(corners_w)])
        opt.add([z3.Or(z3.Not(corners[i][j][k]),
            z3.And(
                z3.And([chip[ii][jj][k] for jj in range(j,j+inst_y[k]) for ii in range(i,i+inst_x[k])]),
                z3.And([z3.Not(chip[ii][jj][k]) for jj in range(0,j) for ii in range(0,chip_w)]),
                z3.And([z3.Not(chip[ii][jj][k]) for jj in range(0,max_h) for ii in range(0,i)]),
                z3.And([z3.Not(chip[ii][jj][k]) for jj in range(j+inst_y[k],max_h) for ii in range(0,chip_w)]),
                z3.And([z3.Not(chip[ii][jj][k]) for jj in range(0,max_h) for ii in range(i+inst_x[k],chip_w)])
            )
        ) for j in range(max_h-inst_y[k]+1) for i in range(chip_w-inst_x[k]+1)])
        opt.add([z3.Or(z3.Not(corners[i][j][k]),z3.And(i<=chip_w-inst_x[k],j<=max_h-inst_y[k])) for j in range(corners_h) for i in range(corners_w)])
        opt.add(z3.Sum([z3.If(corners[i][j][k],1,0) for j in range(corners_h) for i in range(corners_w)])==1)

    
    chip_h = z3.Int('chip_h')
    for k in range(n):
        for i in range(corners_w):
            for j in range(corners_h): 
                opt.add(z3.Or(z3.Not(corners[i][j][k]),chip_h>=j + inst_y[k]))

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