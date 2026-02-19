"""Base class for constraints."""

import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable


class CausalityConstraint(Constraint):
    """Standard exists-constraint."""

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--deterministic",
            action="store_true",
            help="Deterministic Z3 assignment.",
            default=None,
        )
        argument_parser.add_argument(
            "--size", type=int, default=None, help="Fixed size of the cause (number of states in Z)."
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
        exists = z3.And(function(*variables), variables_in_ranges(variables))
         
        # there should only be at least #variables-#size variables set to max(family.hole_options(hole)) + 1
        if self.args.size is not None:
            size_constraint = z3.Sum([z3.If(variables[i] == max(args["family"].hole_options(i)) + 1, 1, 0) for i in range(len(variables))]) >= len(variables) - self.args.size
            print(size_constraint)
            return z3.And(exists, size_constraint)
        else:
            return exists 
