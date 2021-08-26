__version__ = '1.0.0-rc.3'
__author__ = 'Giacomo Berselli, Martino Pulici'


from minizinc import Model, Solver

from vlsi.utilities.plots import *
from vlsi.utilities.preprocessing import *
from vlsi.utilities.wrappers import *
from vlsi.solvers.sat import *
from vlsi.solvers.smt import *


NORMAL = True
ROTATION = True

TIMEOUT_CP = 300
TIMEOUT_SAT = 300
TIMEOUT_SMT = 300

MIN_CP = 1
MAX_CP = 40

MIN_SAT = 1
MAX_SAT = 10

MIN_SMT = 1
MAX_SMT = 40

if TIMEOUT_CP == 0:
    MIN_CP = 41
    MAX_CP = 0
if TIMEOUT_SAT == 0:
    MIN_SAT = 41
    MAX_SAT = 0
if TIMEOUT_SMT == 0:
    MIN_SMT = 41
    MAX_SMT = 0

# Minimum instance
min_ins = min(MIN_CP, MIN_SAT, MIN_SMT)
max_ins = max(MAX_CP, MAX_SAT, MAX_SMT)

# Time lists
times_cp_normal = []
times_sat_normal = []
times_smt_normal = []

# Time lists
times_cp_rotation = []
times_sat_rotation = []
times_smt_rotation = []

# Minizinc solver
solver = Solver.lookup("chuffed")

# Enter if normal configuration is enabled
if NORMAL:
    # Minizinc normal model
    model_normal = Model("src/cp/cp_normal.mzn")

# Enter if rotation configuration is enabled
if ROTATION:
    # Minizinc rotation model
    model_rotation = Model("src/cp/cp_rotation.mzn")

# Cycle instances
for i in range(min_ins, max_ins + 1):
    # File name
    file = str(i)
    # Data dictionary
    data = preprocessing(file)

    if i in range(MIN_CP, MAX_CP + 1) and NORMAL:
        # Solve normal CP
        time = cp_wrapper(
            file,
            data,
            solver,
            model_normal,
            TIMEOUT_CP,
            rotation=False)
        times_cp_normal.append(time)
    else:
        times_cp_normal.append(0)

    if i in range(MIN_CP, MAX_CP + 1) and ROTATION:
        # Solve rotation CP
        time = cp_wrapper(
            file,
            data,
            solver,
            model_rotation,
            TIMEOUT_CP,
            rotation=True)
        times_cp_rotation.append(time)
    else:
        times_cp_rotation.append(0)

    if i in range(MIN_SAT, MAX_SAT + 1) and NORMAL:
        # Solve normal SAT
        time = sat_wrapper(file, data, TIMEOUT_SAT, rotation=False)
        times_sat_normal.append(time)
    else:
        times_sat_normal.append(0)

    if i in range(MIN_SAT, MAX_SAT + 1) and ROTATION:
        # Solve rotation CP
        time = sat_wrapper(file, data, TIMEOUT_SAT, rotation=True)
        times_sat_rotation.append(time)
    else:
        times_sat_rotation.append(0)

    if i in range(MIN_SMT, MAX_SMT + 1) and NORMAL:
        # Solve normal SMT
        time = smt_wrapper(file, data, TIMEOUT_SMT, rotation=False)
        times_smt_normal.append(time)
    else:
        times_smt_normal.append(0)

    if i in range(MIN_SMT, MAX_SMT + 1) and ROTATION:
        # Solve rotation SMT
        time = smt_wrapper(file, data, TIMEOUT_SMT, rotation=True)
        times_smt_rotation.append(time)
    else:
        times_smt_rotation.append(0)

# Time limit
top = max(TIMEOUT_CP, TIMEOUT_SAT, TIMEOUT_SMT)
# Computation times
times = [
    times_cp_normal,
    times_cp_rotation,
    times_sat_normal,
    times_sat_rotation,
    times_smt_normal,
    times_smt_rotation]
# Plot computation times
plot_times(times, min_ins, max_ins, top, NORMAL, ROTATION)
