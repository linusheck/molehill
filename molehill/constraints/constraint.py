"""Base class for constraints."""
import z3
import argparse

class Constraint:
    """Base class for constraints."""
    def __init__(self):
        self.args = None
    
    def solver_settings(self, solver: z3.Solver) -> None:
        """Set custom solver settings here."""

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        """Register arguments for the constraint."""
    
    def set_args(self, args: argparse.Namespace) -> None:
        """Set the arguments for the constraint."""
        self.args = args

    def build_constraint(self, function: z3.Function, variables: list[z3.Var]) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args."""
        raise NotImplementedError("Constraint does not implement build_constraint")

    def show_result(self, model: z3.Model, solver: z3.Solver) -> None:
        """Called after SAT. Print and/or show your result here."""
