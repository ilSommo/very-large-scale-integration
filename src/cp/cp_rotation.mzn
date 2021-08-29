include "globals.mzn";


% Search & restart
int: SEARCH_TYPE = 2;
int: RESTART_TYPE = 4;

% Chip width
int: chip_w;
% Number of circuits
int: n;
% Circuits' range
set of int: RANGE = 1..n;
% Circuits' widths and heights
array[RANGE] of int: inst_x;
array[RANGE] of int: inst_y;
% Minimum and maximum heights
int: min_h;
int: max_h;
% Index of smallest circuit
int: min_index;

% Minimum circuit size
int: min_size = min(inst_x ++ inst_y);
% Chip height
var min_h..max_h: chip_h = max(i in RANGE )(bl_y[i] + new_inst_y[i]);
% Circuits' positions
array[RANGE] of var 0..(chip_w - min_size): bl_x;
array[RANGE] of var 0..(max_h - min_size): bl_y;
% Rotation flags
array[RANGE] of var bool: rotated;
% Actual circuits' widths and heights
array[RANGE] of var int: new_inst_x;
array[RANGE] of var int: new_inst_y;
new_inst_x = [if rotated[k] then inst_y[k] else inst_x[k] endif | k in RANGE];
new_inst_y = [if rotated[k] then inst_x[k] else inst_y[k] endif | k in RANGE];

% Symmetry breaking constraint
constraint symmetry_breaking_constraint(((2 * bl_x[min_index] + new_inst_x[min_index]) <= chip_w) /\ ((2 * bl_y[min_index] + new_inst_y[min_index]) <= chip_h));

% Non-overlapping constraint
constraint diffn(bl_x, bl_y, new_inst_x, new_inst_y);

% Boundaries consistency constraint
constraint forall(i in RANGE) ((bl_x[i] + new_inst_x[i] <= chip_w) /\ (bl_y[i] + new_inst_y[i] <= chip_h));

% Cumulative constraints
constraint cumulative(bl_y, new_inst_y, new_inst_x, chip_w);
constraint cumulative(bl_x, new_inst_x, new_inst_y, chip_h);

% Search type
ann: search_ann = 
  if SEARCH_TYPE == 1 then int_search([chip_h], input_order, indomain_min)
  elseif SEARCH_TYPE == 2 then int_search([chip_h], first_fail, indomain_min)
  elseif SEARCH_TYPE == 3 then int_search([chip_h], dom_w_deg, indomain_min)
  elseif SEARCH_TYPE == 4 then int_search([chip_h], input_order, indomain_random)
  elseif SEARCH_TYPE == 5 then int_search([chip_h], first_fail, indomain_random)
  else int_search([chip_h], dom_w_deg, indomain_random)
  endif;

% Restart type
ann: restart_ann =
  if RESTART_TYPE == 1 then restart_constant(750)
  elseif RESTART_TYPE == 2 then restart_linear(20)
  elseif RESTART_TYPE == 3 then restart_geometric(1.5, 500)
  else restart_luby(250)
  endif;

% Solve CP problem
solve :: search_ann :: restart_ann minimize chip_h;