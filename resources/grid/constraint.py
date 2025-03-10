from molehill.constraints import ExistsConstraint
import z3

class CustomConstraint(ExistsConstraint):
    def build_constraint(self, function, variables, variables_in_ranges):
        return z3.And(super().build_constraint(function, variables, variables_in_ranges), variables[0] + variables[1] == variables[2])
