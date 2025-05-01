"""Base class for constraints."""

import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable


class ExistsForallConstraint(Constraint):
    """Exists-forall-constraint."""

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--forall",
            type=str,
            help="Infix of the forall variables E.g: 'P1 P3' means all variables that contain either P1 or P3.",
            default="sketch_hole",
        )
        argument_parser.add_argument(
            "--random",
            action="store_true",
            help="Random Z3 assignment.",
            default=None,
        )

    def solver_settings(self, solver: z3.Solver) -> None:
        if self.args.random:
            solver.set("phase_selection", 5)

    def build_constraint(
        self,
        function: z3.Function,
        variables: list[z3.Var],
        variables_in_ranges: Callable[[list[z3.Var]], z3.ExprRef],
        **args
    ) -> z3.ExprRef:
        forall_variables = [
            var
            for var in variables
            if any([x in str(var) for x in self.args.forall.split(" ")])
        ]
        if len(forall_variables) == 0:
            raise ValueError("No variables found with the given pattern.")
        var_in_range_statement = variables_in_ranges(variables)
        constraint = z3.And(
            var_in_range_statement,
            z3.ForAll(
                *[forall_variables],
                z3.Implies(var_in_range_statement, function(*variables))
            ),
        )
        return constraint
