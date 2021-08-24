__version__ = '1.0.0-beta.1'
__author__ = 'Giacomo Berselli, Martino Pulici'


from minizinc import Model, Solver

from vlsi.utilities.plots import *
from vlsi.utilities.preprocessing import *
from vlsi.utilities.wrappers import *
from vlsi.solvers.sat import *
from vlsi.solvers.smt import *


NORMAL = True
ROTATION = False

TIMEOUT_CP = 90
TIMEOUT_SAT = 0
TIMEOUT_SMT = 0

MIN_CP = 1
MAX_CP = 40

MIN_SAT = 1
MAX_SAT = 10

MIN_SMT = 32
MAX_SMT = 32

if TIMEOUT_CP == 0:
    MIN_CP = 40
    MAX_CP = 0
if TIMEOUT_SAT == 0:
    MIN_SAT = 40
    MAX_SAT = 0
if TIMEOUT_SMT == 0:
    MIN_SMT = 40
    MAX_SMT = 0

min_ins = min(MIN_CP, MIN_SAT, MIN_SMT)
max_ins = max(MAX_CP, MAX_SAT, MAX_SMT)

times_cp_normal = []
times_sat_normal = []
times_smt_normal = []

times_cp_rotation = []
times_sat_rotation = []
times_smt_rotation = []


solver = Solver.lookup("chuffed")

model_normal = Model("src/cp/cp_normal.mzn")
model_rotation = Model("src/cp/cp_rotation.mzn")


for i in range(min_ins, max_ins + 1):
    file = str(i)
    
    data = preprocessing(file)

    if i in range(MIN_CP, MAX_CP + 1) and NORMAL == True:
        time = cp_wrapper(file,data, solver, model_normal, TIMEOUT_CP, rotation=False)
        times_cp_normal.append(time)
    else:
        times_cp_normal.append(0)

    if i in range(MIN_CP, MAX_CP + 1) and ROTATION == True:
        time = cp_wrapper(file,data, solver, model_rotation, TIMEOUT_CP, rotation=True)
        times_cp_rotation.append(time)
    else:
        times_cp_rotation.append(0)

    if i in range(MIN_SAT, MAX_SAT + 1) and NORMAL == True:
        time = sat_wrapper(file,data, TIMEOUT_SAT, rotation=False)
        times_sat_normal.append(time)  
    else:
        times_sat_normal.append(0)
    
    if i in range(MIN_SAT, MAX_SAT + 1) and ROTATION == True and False:
        time = sat_wrapper(file,data, TIMEOUT_SAT, rotation=True)
        times_sat_rotation.append(time)  
    else:
        times_sat_rotation.append(0)


    if i in range(MIN_SMT, MAX_SMT + 1) and NORMAL == True:
        time = smt_wrapper(file,data, TIMEOUT_SMT, rotation=False)
        times_smt_normal.append(time)  
    else:
        times_smt_normal.append(0)
    
    if i in range(MIN_SMT, MAX_SMT + 1) and ROTATION == True:
        time = smt_wrapper(file,data, TIMEOUT_SMT, rotation=True)
        times_smt_rotation.append(time)  
    else:
        times_smt_rotation.append(0)


top = max(TIMEOUT_CP, TIMEOUT_SAT, TIMEOUT_SMT)
times = [times_cp_normal,times_cp_rotation, times_sat_normal,times_sat_rotation, times_smt_normal, times_smt_rotation]
plot_times(times, min_ins, max_ins, top, NORMAL, ROTATION)
