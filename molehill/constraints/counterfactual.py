"""Base class for constraints."""

import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable


class CounterfactualConstraint(Constraint):
    """Counterfactual constraint."""

    def __init__(self):
        super().__init__()
        self.num_var_in_cause = z3.Int("num_var_in_cause")
        self.var_in_cause = None
        self.actual_values = None
        self.variables = None
    
    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--deterministic",
            action="store_true",
            help="Deterministic Z3 assignment.",
            default=None,
        )
        argument_parser.add_argument(
            "--cause-size",
            type=int,
            help="Maximum size of the cause.",
            default=1,
        )
        argument_parser.add_argument(
            "--actual",
            type=str,
            help="Actual world, with key=value pairs separated by commas followed by spaces.",
            default=None,
        )
        argument_parser.add_argument(
            "--actual-sched",
            type=str,
            help="Scheduler JSON file containing actual world",
            default=None,
        )


    def solver_settings(self, solver: z3.Solver) -> None:
        if not self.args.deterministic:
            # Random phase selection works well here
            solver.set("phase_selection", 5)

    def build_constraint(
        self,
        function: z3.Function,
        variables: list[z3.Var],
        variables_in_ranges: Callable[[list[z3.Var]], z3.ExprRef],
        **args
    ) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args."""
        self.variables = variables

        family = args["family"]

        constraints = []

        self.var_in_cause = [z3.Bool(f"cause_{i}") for i in range(len(variables))]

        constraints.append(
            self.num_var_in_cause == z3.Sum([z3.If(v, 1, 0) for v in self.var_in_cause])
        )
        constraints.append(self.num_var_in_cause >= 1)
        constraints.append(self.num_var_in_cause <= self.args.cause_size)

        self.actual_values = {}
        hole_to_name_without_spaces = [x.replace(" ", "").replace("\t", "") for x in family.hole_to_name]
        if self.args.actual is not None:
            if self.args.actual.endswith(".txt"):
                with open(self.args.actual, "r", encoding="utf-8") as f:
                    self.args.actual = f.read().strip()
            actual_assignments = self.args.actual.split(", ")
            def process_variable_name(name: str) -> str:
                return name.strip().replace(" ", "").replace("\t", "")
            for assignment in actual_assignments:
                split = assignment.split("=")
                key = "=".join(split[:-1])
                value = split[-1]
                key = process_variable_name(key)
                value = value.strip()
                if not key in hole_to_name_without_spaces:
                    raise ValueError(f"Unknown variable in actual world: {key}")
                hole_num = hole_to_name_without_spaces.index(key)
                if not value in family.hole_to_option_labels[hole_num]:
                    raise ValueError(f"Unknown value for variable {key} in actual world: {value}")
                val = family.hole_to_option_labels[hole_num].index(value)
                found_var = False
                for i, var in enumerate(variables):
                    if process_variable_name(var.decl().name()) == key:
                        found_var = True
                        constraints.append(
                            self.var_in_cause[hole_num] == (self.variables[hole_num] != int(val))
                        )
                        self.actual_values[hole_num] = int(val)
                        break
                assert found_var, f"Could not find variable {key} in variables"

        constraints.append(variables_in_ranges(variables))

        constraints.append(z3.Not(function(*variables))) # This is the counterfactual world

        return z3.And(*constraints)

    def optimize(self) -> z3.ExprRef:
        """Optimize something?"""
        return self.num_var_in_cause
    
    def show_result(self, model, solver, **args):
        print()
        family = args["family"]
        cause = []
        counterfactual = []
        for i in range(len(self.variables)):
            if model[self.var_in_cause[i]]:
                print(f"Variable in cause: {family.hole_to_name[i]}")
                 # If we don't know the actual value, just print "?"
                if not i in self.actual_values:
                    cause.append("?")
                else:
                    option = family.hole_options_to_string(i, [self.actual_values[i]])
                    cause.append(option)
                counterfactual_value = model[self.variables[i]]
                counterfactual.append(family.hole_options_to_string(i, [counterfactual_value.as_long()]))
        print("Cause:", ", ".join(cause))
        print("Counterfactual:", ", ".join(counterfactual))

# Dead research code:

# # TODO This doesn't work yet
# elif self.args.actual_sched is not None:
#     num_assignments = 0
#     import json
#     with open(self.args.actual_sched, "r", encoding="utf-8") as f:
#         sched = json.load(f)
#     # Use the entire scheduler as the actual world
#     # Each state corresponds to a single hole assignment
#     counter = -1
#     for idx, state in enumerate(sched):
#         if len(state["c"][0]["labels"]) == 0:
#             continue
#         # print(state["c"])
#         counter += 1
#         # actual_state = state["s"]
#         # # actual state: {'s1': 0, 's2': 0, 'w12': 0, 'w21': 0, 'x1': 0, 'x2': 0, 'y1': 0, 'y2': 0, 'z1': 0, 'z2': 0}
#         # # corresponding hole name: A([s1=0&s2=0&w12=0&w21=0&x1=0&x2=0&y1=0&y2=0&z1=0&z2=0],0)
#         # corresponding_hole_name = f"A([{ '&'.join(f'{k}={v}' for k, v in actual_state.items()) }],0)"
#         # print(hole_to_name_without_spaces)
#         # print(corresponding_hole_name)
#         # if corresponding_hole_name not in hole_to_name_without_spaces:
#         #     assert len(state["c"][0]["labels"]) == 0, str(state["c"][0]["labels"])
#         #     continue
#         # print(state["s"])
#         hole_num = counter #hole_to_name_without_spaces.index(corresponding_hole_name)
#         if len(state["c"][0]["labels"]) == 0:
#             continue
#         value_str = state["c"][0]["labels"][0]

#         if value_str not in family.hole_to_option_labels[hole_num]:
#             raise ValueError(f"Unknown value for variable {value_str} in actual world: {family.hole_to_option_labels[hole_num]}")
#         val = family.hole_to_option_labels[hole_num].index(value_str)
#         # Only set for the corresponding hole
#         constraints.append(
#             self.var_in_cause[hole_num] == (self.variables[hole_num] != int(val))
#         )
#         self.actual_values[hole_num] = int(val)
#         # print(f"Actual assignment: {hole_num} -> {val}")
#         num_assignments += 1
#     # print(f"Total assignments in actual world: {num_assignments}")
#     # print(f"Total holes: {len(variables)}")