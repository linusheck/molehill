import z3
from molehill.constraints import Constraint

class CustomConstraint(Constraint):
    def build_constraint(self, function, variables, variables_in_ranges, **args):
        def different(variable_names):
            z3_vars = [v for v in variables if str(v) in variable_names]
            assert len(z3_vars) == len(variable_names)
            return z3.Distinct(z3_vars)

        different_vars = [
            ["X2333_32", "X2333_13", "X2333_22"],
            ["X3233_23", "X3233_31", "X3233_22"],
            ["X132333_32", "X132333_12", "X132333_22"],
            ["X313233_23", "X313233_21", "X313233_22"],
            ["X233233_31", "X233233_13", "X233233_22"],
            ["X23313233_13", "X23313233_21", "X23313233_22"],
            ["X13233233_12", "X13233233_31", "X13233233_22"],
            ["X1323313233_12", "X1323313233_21", "X1323313233_22"],
        ]

        constraint = [different(variable_names) for variable_names in different_vars] + [variables_in_ranges(variables), function(*variables)]
        return z3.And(constraint)

