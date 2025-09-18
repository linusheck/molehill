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

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--deterministic",
            action="store_true",
            help="Deterministic Z3 assignment.",
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
        self.counterfactual_vars = [z3.Const(f"counterfactual_{var}", var.sort()) for i, var in enumerate(variables)]

        # if you change any variable in cause_variables, the function should not hold anymore

        constraints = []
        
        constraints.append(variables_in_ranges(variables))
        constraints.append(variables_in_ranges(self.counterfactual_vars))

        constraints.append(function(*variables)) # This is the actual world
        constraints.append(z3.Not(function(*self.counterfactual_vars))) # This is the counterfactual world

        self.var_in_cause = [z3.Bool(f"cause_{i}") for i in range(len(variables))]

        for i in range(len(variables)):
            constraints.append(
                self.var_in_cause[i] == (self.variables[i] == self.counterfactual_vars[i])
            )
        
        
        constraints.append(
            self.num_var_in_cause == z3.Sum([z3.If(v, 1, 0) for v in self.var_in_cause])
        )
        constraints.append(self.num_var_in_cause >= 1)

        return z3.And(*constraints)

    def optimize(self) -> z3.ExprRef:
        """Optimize something?"""
        return self.num_var_in_cause
    
    def show_result(self, model, solver, **args):
        cause = []
        for i in range(len(self.variables)):
            if model[self.var_in_cause[i]]:
                cause.append(f"{self.variables[i]} == {model[self.variables[i]]}")
        print("Cause:", ", ".join(cause))
