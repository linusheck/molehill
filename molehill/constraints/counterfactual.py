import z3
import argparse
from molehill.constraints.constraint import Constraint
from typing import Callable

class CounterfactualConstraint(Constraint):
    """
    Encodes the 'Partial Scheduler Cause' definition for SMPMC.
    
    Synthesizes a partial scheduler psi (defined by a mask Z and values from 'variables')
    that satisfies:
    - AC1: The full scheduler 'variables' satisfies the spec (phi).
    - AC2(a): Existence of a counterfactual (pi') that deviates from psi and violates phi.
    - AC2(b): Robustness/Sufficiency: All extensions of psi satisfy phi.
    """

    def __init__(self):
        super().__init__()
        self.num_var_in_cause = z3.Int("num_var_in_cause")
        self.var_in_cause = None  # The set Z (boolean mask)
        self.variables = None     # The actual scheduler (pi)
        self.cf_variables = None  # The counterfactual scheduler (pi')
        self.rob_variables = None # The robustness quantifier variables (pi'')

    def register_arguments(self, argument_parser: argparse.ArgumentParser) -> None:
        argument_parser.add_argument(
            "--size", type=int, default=None, help="Fixed size of the cause (number of states in Z)."
        )
        argument_parser.add_argument(
            "--ac2b", type=bool, default=True,
        )

    def build_constraint(
        self,
        function: z3.Function,
        variables: list[z3.Var],
        variables_in_ranges: Callable[[list[z3.Var]], z3.ExprRef],
        **args
    ) -> z3.ExprRef:
        self.variables = variables
        constraints = []
        n = len(variables)

        self.var_in_cause = [z3.Bool(f"in_cause_{i}") for i in range(n)]

        constraints.append(
            self.num_var_in_cause == z3.Sum([z3.If(v, 1, 0) for v in self.var_in_cause])
        )
        if self.args.size is not None:
            constraints.append(self.num_var_in_cause <= self.args.size)

        # Helper: Check if a scheduler 'target' agrees with the cause 'source' on Z
        # psi <= target
        def agrees_on_cause(source, target):
            return z3.And([
                z3.Implies(self.var_in_cause[i], source[i] == target[i])
                for i in range(n)
            ])

        # AC1
        # The synthesized 'variables' (pi) must satisfy the specification.
        constraints.append(variables_in_ranges(self.variables))
        constraints.append(function(*self.variables))

        # AC2(a)
        self.cf_variables = [z3.Const(f"cf_{i}", v.sort()) for i, v in enumerate(variables)]
        
        constraints.append(variables_in_ranges(self.cf_variables))
        constraints.append(z3.Not(agrees_on_cause(variables, self.cf_variables)))
        constraints.append(z3.Not(function(*self.cf_variables)))

        # AC2(b)
        self.rob_variables = [z3.Const(f"rob_{i}", v.sort()) for i, v in enumerate(variables)]

        if self.args.ac2b:
            robustness_condition = z3.ForAll(
                self.rob_variables,
                z3.Implies(
                    z3.And(
                        variables_in_ranges(self.rob_variables),
                        agrees_on_cause(variables, self.rob_variables)
                    ),
                    function(*self.rob_variables)
                )
            )
            constraints.append(robustness_condition)

        return z3.And(*constraints)

    def show_result(self, model, solver, **args):
        family = args.get("family")

        print("\n")
        print("Actual Scheduler (Satisfies Spec):")
        actual_elements = []
        for i in range(len(self.variables)):
            val = model[self.variables[i]].as_long()
            val_str = family.hole_options_to_string(i, [val]) if family else str(val)
            actual_elements.append(f"State {i}: {val_str}")
        print("{ " + ", ".join(actual_elements) + " }")

        cause_elements = []
        for i, in_cause in enumerate(self.var_in_cause):
            if model[in_cause]:
                val = model[self.variables[i]].as_long()
                val_str = family.hole_options_to_string(i, [val]) if family else str(val)
                cause_elements.append(f"State {i}: {val_str}")
        
        print(f"Cause (Size {len(cause_elements)}):")
        print("{ " + ", ".join(cause_elements) + " }")

        print("\n\"Repair\" Counterfactual:")
        cf_diff = []
        for i, cf_var in enumerate(self.cf_variables):
            is_in_z = model[self.var_in_cause[i]]
            actual_val = model[self.variables[i]]
            cf_val = model[cf_var]
            
            if is_in_z and (actual_val.as_long() != cf_val.as_long()):
                val_str = family.hole_options_to_string(i, [cf_val.as_long()]) if family else str(cf_val)
                cf_diff.append(f"State {i} (in Z) changed to {val_str}")
                
        print(", ".join(cf_diff))
        print("\n")
