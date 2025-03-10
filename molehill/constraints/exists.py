"""Base class for constraints."""

import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable


class ExistsConstraint(Constraint):
    """Standard exists-constraint."""

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
    ) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args."""
        return z3.And(function(*variables), variables_in_ranges(variables))
