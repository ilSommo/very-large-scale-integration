import z3
import time

def smt(chip_w, n, inst_x, inst_y):
    opt = z3.Optimize()
    opt.set("timeout", 10000)

    max_h = sum(inst_y) - min(inst_y)

    bl_x = z3.IntVector('bl_x', n)
    bl_y = z3.IntVector('bl_y', n)
    b = [[z3.Int("b_%s_%s" % (i, j)) for j in range(max_h) ] for i in range(chip_w)]

    for x, y in zip(bl_x, bl_y):
        opt.add(x >=0)
        opt.add(x <= chip_w - min(inst_x))
        opt.add(y >=0)
        opt.add(y <= chip_w - min(inst_y))

    for row in b:
        for elem in row:
            opt.add(elem >= 0)
            opt.add(elem <= n)

    for i in range(chip_w):
        for j in range(max_h):
            for v in range(n):
                opt.add((b[i][j] == v) == z3.And(i>bl_x[v], i<=bl_x[v]+inst_x[v], j>bl_y[v], j<=bl_y[v]+inst_y[v]))

    for i in range(n):
        opt.add(bl_x[i]+inst_x[i] <= chip_w)

    chip_h = z3.Int('chip_h')

    for i in range(n):
        opt.add(chip_h>=bl_y[i] + inst_y[i])
    
    opt.minimize(chip_h)
<<<<<<< HEAD
    start = time.time() 
=======
    
    start = time.time()
>>>>>>> SAT-gym
    opt.check()
    end = time.time()
    model=opt.model()
    result_x=[]
    result_y=[]
    try:
        for i in range(n):
            result_x.append(int(str(model.evaluate(bl_x[i]))))
            result_y.append(int(str(model.evaluate(bl_y[i]))))
        chip_h_int = int(str(model.evaluate(chip_h)))
    except:
        chip_h_int = 0

    

    return chip_h_int, result_x, result_y, end-start