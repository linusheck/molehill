"""A pure SMT approach. Bad performance, but good comparison."""

import z3
from molehill.constraints import Constraint
from stormpy import model_checking
from fractions import Fraction

def get_constraints(variables_in_bounds, quotient):
    def build(*variables):
        quotient.build(quotient.family)

        transition_matrix = quotient.family.mdp.model.transition_matrix

        choice_to_assignment = quotient.coloring.getChoiceToAssignment()

        target_states = model_checking(quotient.family.mdp.model, quotient.specification.all_properties()[0].formula.subformula.subformula).get_truth_values()

        assertions = []

        initial_state = quotient.family.mdp.model.initial_states[0]
        assert len(quotient.family.mdp.model.initial_states) == 1, "ProbGoal only supports single initial states."

        variable_types = [z3.BitVecSort(variable.size()) for variable in variables]

        print("Number of rows:", transition_matrix.nr_rows)

        spec = quotient.specification
        print(spec)
        prop = spec.all_properties()[0]

        # assert that prop.formula is a reachability property
        assert prop.formula.subformula.is_eventually_formula

        prop_str = str(prop)
        is_prob = prop_str.startswith("P")

        comparison_term = prop_str.split()[0][1:]

        # comparison_term is either >x, >=x, <x, <=x
        # we need to extract the number x and the operator
        comparators = [">=", "<=", ">", "<"]
        for comparator in comparators:
            if comparator in comparison_term:
                comparison_value = float(Fraction(comparison_term.split(comparator)[1]))
                comparison_operator = comparator
                break

        reward_model = None
        if not is_prob:
            prop_prefix = prop_str.split(comparator)[0]
            # example: R{"coin_flips"}>=1/2
            # get coin_flips
            assert prop_prefix.startswith("R{") and prop_prefix.endswith("}"), "Property must be a reachability property with a reward model."
            # extract the reward model name
            reward_model_name = prop_prefix[3:prop_str.index("\"}")]
            # get the reward model
            reward_model = quotient.family.mdp.model.reward_models[reward_model_name]

        z3_comparators = {
            ">=": lambda a, b: a >= b,
            "<=": lambda a, b: a <= b,
            ">": lambda a, b: a > b,
            "<": lambda a, b: a < b
        }
        z3_compare = z3_comparators[comparison_operator]

        reachability_vars = []
        for state in range(transition_matrix.nr_columns):
            reach_var = z3.Function(f"reach_{state}", *variable_types, z3.BoolSort())
            reachability_vars.append(reach_var)

        min_step_vars = []
        for state in range(transition_matrix.nr_columns):
            min_step_var = z3.Function(f"min_step_{state}", *variable_types, z3.IntSort())
            min_step_vars.append(min_step_var)
            assertions.append(min_step_var(*variables) >= 0)

        for state in range(transition_matrix.nr_columns):
            if target_states.get(state):
                assertions.append(reachability_vars[state](*variables))
                assertions.append(min_step_vars[state](*variables) == 0)
                continue
            
            statement_for_state = []
            
            rows = transition_matrix.get_rows_for_group(state)
            for row in rows:
                assignment = choice_to_assignment[row]
                assignment_as_z3 = z3.And([
                    variables[var] == z3.BitVecVal(x, variables[var].size())
                    for var, x in assignment
                ])

                reachability_vars_of_row = []
                min_step_vars_of_row = []

                for entry in transition_matrix.get_row(row):
                    value = entry.value()
                    if value == 0:
                        continue
                    assert value > 0, "Transition probabilities must be positive."
                    to_state = entry.column
                    if to_state == state:
                        continue
                    reachability_vars_of_row.append(reachability_vars[to_state](*variables))
                    min_step_vars_of_row.append(min_step_vars[to_state](*variables))
                statement_for_state.append(z3.Implies(assignment_as_z3, z3.Or(reachability_vars_of_row)))
                assertions.append(
                    z3.Implies(
                        z3.And(reachability_vars[state](*variables), assignment_as_z3),
                        z3.And(
                            z3.Or([min_step_vars[state](*variables) == x + 1 for x in min_step_vars_of_row]),
                            z3.And([min_step_vars[state](*variables) <= x + 1 for x in min_step_vars_of_row])
                        )
                    )
                )
            assertions.append(z3.Implies(reachability_vars[state](*variables), z3.Or(statement_for_state)))

        value_vars = []
        for state in range(transition_matrix.nr_columns):
            value_var = z3.Function(f"value_{state}", *variable_types, z3.RealSort())
            value_vars.append(value_var)
            assertions.append(value_var(*variables) >= 0)
            if is_prob:
                assertions.append(value_var(*variables) <= 1)

        for state in range(transition_matrix.nr_columns):
            if target_states.get(state):
                if is_prob:
                    assertions.append(value_vars[state](*variables) == z3.RealVal(1))
                else:
                    assertions.append(value_vars[state](*variables) == z3.RealVal(0))
                assertions.append(reachability_vars[state](*variables))
                continue

            statement_for_state = []
            
            rows = transition_matrix.get_rows_for_group(state)
            for row in rows:
                assignment = choice_to_assignment[row]
                assignment_as_z3 = z3.And([
                    variables[var] == z3.BitVecVal(x, variables[var].size())
                    for var, x in assignment
                ])

                value_vars_of_row = []
                if reward_model:
                    reward = reward_model.get_state_action_reward(row)
                    value_vars_of_row.append(z3.RealVal(reward))
                for entry in transition_matrix.get_row(row):
                    value = entry.value()
                    if value == 0:
                        continue
                    assert value > 0, "Transition probabilities must be positive."
                    to_state = entry.column
                    value_vars_of_row.append(z3.RealVal(value) * value_vars[to_state](*variables))
                statement_for_state.append(z3.Implies(assignment_as_z3, value_vars[state](*variables) == z3.Sum(value_vars_of_row)))
            assertions.append(z3.And(statement_for_state))
            assertions.append(z3.Implies(z3.Not(reachability_vars[state](*variables)), value_vars[state](*variables) == z3.RealVal(0)))
        assertions.append(z3_compare(value_vars[initial_state](*variables), z3.RealVal(comparison_value)))

        print("Done with assertions")
        return z3.And(*assertions)
    return build
