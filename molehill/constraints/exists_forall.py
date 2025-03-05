"""Base class for constraints."""
import z3
import argparse
from molehill.constraints.constraint import Constraint

class ExistsForallConstraint(Constraint):
    """Standard exists-constraint."""
    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--forall",
            type=str,
            help="Infix of the forall variables E.g: 'P1 P3' means all variables that contain either P1 or P3.",
            required=True,
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

    def build_constraint(self, function: z3.Function, variables: list[z3.Var]) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args."""
        forall_variables = [var for var in variables if any([x in str(var) for x in self.args.forall.split(" ")])]
        if len(forall_variables) == 0:
            raise ValueError("No variables found with the given pattern.")
        return z3.ForAll(*[forall_variables], function(*variables))
