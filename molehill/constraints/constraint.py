"""Base class for constraints."""
import z3
import argparse

class Constraint:
    """Base class for constraints."""
    def __init__(self):
        pass

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        """Register arguments for the constraint."""

    def build_constraint(self, variables: list[z3.Var], args: argparse.Namespace) -> z3.ExprRef:
        """Implement your constraint here. Arguments are passed by args."""

    def show_result(self, model: z3.Model, solver: z3.Solver) -> None:
        """Called after SAT. Print and/or show your result here."""
