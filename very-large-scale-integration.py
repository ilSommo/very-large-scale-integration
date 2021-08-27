__version__ = '1.0.0-rc.4'
__author__ = 'Giacomo Berselli, Martino Pulici'


from minizinc import Model, Solver

from vlsi.utilities.plots import plot_times
from vlsi.utilities.preprocessing import preprocessing
from vlsi.utilities.wrappers import cp_wrapper, sat_wrapper, smt_wrapper

REPORT = False

NORMAL = True
ROTATION = False

TIMEOUT_CP = 0
TIMEOUT_SAT = 300
TIMEOUT_SMT = 0

MIN_CP = 1
MAX_CP = 40

MIN_SAT = 1
MAX_SAT = 1

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

times_null = []

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

    times_null.append(0)

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
if REPORT == False:
    plot_times(times, min_ins, max_ins, top, NORMAL, ROTATION,'')
else:
    plot_times(times, min_ins, max_ins, top, NORMAL, ROTATION,'')
    plot_times([times_cp_normal,times_cp_rotation,times_null,times_null,times_null,times_null], min_ins, max_ins, top, True, True,'-cp')
    plot_times([times_null,times_null,times_sat_normal,times_sat_rotation,times_null,times_null], min_ins, max_ins, top, True, True,'-sat')
    plot_times([times_null,times_null,times_null,times_null,times_smt_normal,times_smt_rotation], min_ins, max_ins, top, True, True,'-smt')
    plot_times([times_cp_normal,times_null,times_sat_normal,times_null,times_smt_normal,times_null], min_ins, max_ins, top, True, False,'-normal')
    plot_times([times_null,times_cp_rotation,times_null,times_sat_rotation,times_null,times_smt_rotation], min_ins, max_ins, top, False, True,'-rotation')
