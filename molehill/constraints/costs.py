"""Costs Constraint with costs loaded from a file."""

import z3
import os
from molehill.constraints import Constraint


class CostsConstraint(Constraint):

    COSTS_FILE = "sketch.costs"

    def __init__(self, project_path=None):
        self.project_path = project_path
        self.costs_threshold = None

    def register_arguments(self, argument_parser):
        argument_parser.add_argument(
            "--costs-threshold",
            type=int,
            help="Threshold for the costs constraint.",
            default=None,
        )

    def build_constraint(self, function, variables, variables_in_ranges, **args):
        # We build the quotient here

        quotient = args["quotient"]
        self.costs_threshold = self.args.costs_threshold

        assertions = []
        
        lines = None
        costs_path = self.project_path + "/" + self.COSTS_FILE
        with open(costs_path, "r") as f:
            lines = f.readlines()

        cost_vars = []
        line_index = 0
        for hole in range(quotient.family.num_holes):
            for option in range(quotient.family.hole_num_options(hole)):
                hole_name = quotient.family.hole_name(hole)
                cost_var = z3.Int(f"cost_{hole_name}_{option}")
                cost_vars.append(cost_var)
                line = lines[line_index].strip()
                line_index += 1
                line_hole, line_option, cost_value = line.split()
                assert line_hole == hole_name, f"Expected hole {hole_name}, got {line_hole}"
                assert int(line_option) == option, f"Expected option {option}, got {line_option}"

                assertions.append(
                    z3.If(
                        variables[hole] == z3.BitVecVal(option, variables[hole].size()),
                        cost_var == int(cost_value),
                        cost_var == 0
                    )
                )

        # Add constraint: sum of cost_vars <= costs_threshold
        assertions.append(z3.Sum(cost_vars) <= self.costs_threshold)
        
        return assertions + [variables_in_ranges(variables), function(*variables)]
        