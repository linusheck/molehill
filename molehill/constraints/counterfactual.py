"""Base class for constraints."""

import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable


class CounterfactualConstraint(Constraint):
    """Counterfactual constraint."""

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

        # if you change any variable in cause_variables, the function should not hold anymore

        constraints = []
        
        constraints.append(function(*variables))
        constraints.append(variables_in_ranges(variables))

        cause_sets = []
        self.cause_sets = cause_sets

        alternative_sets = []
        self.alternative_sets = alternative_sets

        for j in range(1):
            # We search for one counterfactual cause for the assignment
            cause_variables = [z3.Bool(f"cause_var_{i}_{j}") for i in range(len(variables))]
            cause_sets.append(cause_variables)


            # # all extensions of the cause variables must satisfy the function
            # forall_vars = [z3.BitVec(f"forall_var_{i}", variables[0].sort().size()) for i in range(len(variables))]
            # constraints.append(z3.ForAll(
            #     forall_vars,
            #     z3.Implies(variables_in_ranges(forall_vars),
            #     function(*[
            #         z3.If(cause_variables[k], variables[k], forall_vars[k])
            #         for k in range(len(variables))
            #     ]))))



            # for i, var in enumerate(variables):
            #     alternative_vars = [z3.BitVec(f"alternative_var_{i}_{j}_{k}", variables[i].sort().size()) for k in range(len(variables))]
            #     constraints.append(variables_in_ranges(alternative_vars))
            #     constraints.append(
            #         z3.Not(function(*[
            #             z3.If(cause_variables[k] if k != i else True, variables[k], alternative_vars[k])
            #             for k in range(len(variables))
            #         ]))
            #     )

            constraints.append(z3.Or(*cause_variables)) 
        print(constraints)
        # cause sets are different from each other
        # for i in range(len(cause_sets)):
        #     for j in range(i + 1, len(cause_sets)):
        #         constraints.append(z3.Or([cause_sets[i][k] != cause_sets[j][k] for k in range(len(cause_sets[i]))]))

        return z3.And(*constraints)
    
    def show_result(self, model, solver, **args):
        print(model)
        for j in range(len(self.cause_sets)):
            cause = []
            cause_variables = self.cause_sets[j]
            for i in range(len(cause_variables)):
                if model[cause_variables[i]]:
                    cause.append(f"{self.variables[i]} == {model[self.variables[i]]}")
            print(", ".join(cause))
