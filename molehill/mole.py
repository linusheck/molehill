"""Molehill's core mechanism."""

from settrie import SetTrie
from stormpy import model_checking, CheckTask
from decimal import Decimal
from fastmole import MatrixGeneratorDouble, MatrixGeneratorRationalNumber
from molehill.counterexamples import check
from molehill.plugin import SearchMarkovChain
import time
import z3


class Mole:
    def __init__(
        self,
        solver,
        variables,
        quotient,
        exact=False,
        draw_image=False,
        considered_counterexamples="all"
    ):
        self.quotient = quotient
        self.exact = exact
        # models we have already analyzed
        self.all_violated_models = [SetTrie(), SetTrie()]
        self.inconclusive_models = [SetTrie(), SetTrie()]

        self.considered_models = 0
        self.mc_calls = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()

        quotient.build(quotient.family)

        print("Family size", "{:.2e}".format(Decimal(self.quotient.family.size)))
        print("Quotient size", self.quotient.family.mdp.model.nr_states)

        # reasons for new assertion
        self.reasons = []

        self.fixed_something = False

        # TODO: We should definitely check that there are no nontrivial end components

        # if prop.formula.optimality_type == OptimizationDirection.Maximize:
        #     bad_states, good_states = prob01max_states(self.quotient.family.mdp.model, prop.formula.subformula)
        # elif prop.formula.optimality_type == OptimizationDirection.Minimize:
        #     bad_states, good_states = prob01min_states(self.quotient.family.mdp.model, prop.formula.subformula)
        # else:
        #     raise ValueError("Unknown operator in property")

        # # check whether there are nontrivial end components
        # maximal_end_components = get_maximal_end_components(quotient.family.mdp.model)
        # for maximal_end_component in maximal_end_components:
        #     for state, _choices in maximal_end_component:
        #         if state not in good_states and state not in bad_states:
        #             raise ValueError("Nontrivial end component")

        # because the quotient has no nontrivial end component, no sub-MDP does either :)

        self.complete_transition_matrix = (
            self.quotient.family.mdp.model.transition_matrix
        )
        assert len(self.quotient.family.mdp.model.initial_states) == 1

        # target_states == states with target label
        self.matrix_generators = {}

        self.mdp_fails_and_wins = [0, 0]

        self.draw_image = draw_image
        if self.draw_image:
            self.image_assertions = []
        self.considered_counterexamples = considered_counterexamples
        self.counterexamples = []

        self.plugin = SearchMarkovChain(solver, None, self)
        self.variables = variables
        self.model_variable_names = [str(x) for x in variables]

        self.first_dtmc_checked = False

        self.function_argument_tracker = []

    def get_matrix_generator(self, invert=False):
        if invert in self.matrix_generators:
            return self.matrix_generators[invert]

        spec = self.quotient.specification
        if invert:
            spec = spec.negate()
        prop = spec.all_properties()[0]
        check_task = CheckTask(prop.formula)

        # does there exist a model that satisfies the property?
        # print("Quotient size", self.quotient.family.mdp.model.nr_states)
        result = model_checking(self.quotient.family.mdp.model, prop.formula)
        global_bounds = result.get_values()

        target_states = model_checking(
            self.quotient.family.mdp.model, prop.formula.subformula.subformula
        ).get_truth_values()
        if self.exact:
            # We need to use rational numbers for exactness
            generator = MatrixGeneratorRationalNumber(
                self.quotient.family.mdp.model,
                check_task,
                target_states,
                global_bounds,
                self.choice_to_assignment,
            )
        else:
            generator = MatrixGeneratorDouble(
                self.quotient.family.mdp.model,
                check_task,
                target_states,
                global_bounds,
                self.choice_to_assignment,
            )
        self.matrix_generators[invert] = generator
        return generator

    def partial_model_consistent(self, partial_model, invert=False):
        """Analyze the current sub-MDP and (perhaps) push theory lemmas."""

        if time.time() - self.time_last_print > 1:
            print(f"Considered {self.mc_calls} models so far (cache hits: {self.considered_models - self.mc_calls})")
            self.time_last_print = time.time()

        num_fixed = len(partial_model.keys())
        model = "DTMC" if num_fixed == len(self.model_variable_names) else "MDP"

        # This is a magic trick to make sure we first check a DTMC after the
        # quotient. I believe that it's really helpful, e.g., in MDPs, where we
        # can just check a Markov chain first if the quotient is not violated.
        if model == "DTMC":
            self.first_dtmc_checked = True
        if model == "MDP" and not self.first_dtmc_checked and len(partial_model) > 0:
            return False, None

        self.considered_models += 1

        frozen_partial_model = set(map(lambda x: f"{x[0]}={x[1]}", partial_model.items()))
        conflicts_violated = list(self.all_violated_models[int(invert)].subsets(
            frozen_partial_model
        ))
        if len(conflicts_violated) > 0:
            conflict_indices = min([eval(x) for x in conflicts_violated], key=len)
            conflict = [self.model_variable_names[i] for i in conflict_indices]
            return True, conflict

        conflicts_inconclusive = self.inconclusive_models[int(invert)].supersets(
            frozen_partial_model
        )
        if len(conflicts_inconclusive) > 0:
            return False, None

        # If the set intersects with a set where we have proven the opposite, 
        # we can just return False.
        # This holds for subsets:
        conflicts_inverse_violated_sub = self.all_violated_models[1 - int(invert)].subsets(
            frozen_partial_model
        )
        if len(conflicts_inverse_violated_sub) > 0:
            return False, None
        # And supersets:
        conflicts_inverse_violated_super = self.all_violated_models[1 - int(invert)].supersets(
            frozen_partial_model
        )
        if len(conflicts_inverse_violated_super) > 0:
            return False, None

        # Make a PAYNT family from the current partial model.
        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.model_variable_names[hole]
            if var in partial_model:
                new_family.hole_set_options(hole, [partial_model[var]])
        

        # Prop is always rechability, even if our input was until (thanks paynt :)).
        prop = self.quotient.specification.all_properties()[0]
        if invert:
            prop = self.quotient.specification.negate().all_properties()[0]

        # print("Check", new_family, prop)

        # Decide whether we want to compute a counterexample.
        compute_counterexample = True
        remove_optimal_holes = True
        if self.considered_counterexamples == "none":
            compute_counterexample = False
            remove_optimal_holes = False
        elif self.considered_counterexamples == "sched":
            compute_counterexample = False
        elif self.considered_counterexamples == "mc" and model == "MDP":
            compute_counterexample = False

        # Check the sub-MDP (see counterexample.py).
        check_result = check(
            self.get_matrix_generator(invert),
            new_family,
            prop,
            compute_counterexample,
            remove_optimal_holes,
        )
        self.mc_calls += 1
        all_violated = check_result.all_schedulers_violate
        # print("All violated", all_violated, check_result.result.at(0))
        counterexample = check_result.fixed_holes

        # Keep track of MDP fails and wins.
        if model == "MDP":
            if all_violated:
                self.mdp_fails_and_wins[1] += 1
            else:
                self.mdp_fails_and_wins[0] += 1
        if all_violated:
            # Push a reason (explain).
            if len(counterexample) < num_fixed:
                self.reasons.append(
                    f"{model} counterexample {num_fixed}->{len(counterexample)} ({partial_model})"
                )
            else:
                self.reasons.append(f"{model} reject {num_fixed}")

            # If we want to draw a nice image, we need this statement.
            if self.draw_image:
                term = z3.Not(
                    z3.And(
                        [
                            self.variables[c] == partial_model[str(self.variables[c])]
                            for c in counterexample
                        ]
                    ),
                )
                self.image_assertions.append(term)
                self.counterexamples.append(
                    (
                        self.model_variable_names[c],
                        partial_model[str(self.variables[c])],
                    )
                    for c in counterexample
                )

            counterexample_names = [self.model_variable_names[i] for i in counterexample]
            filtered_partial_model = {name: partial_model[name] for name in counterexample_names}
            filtered_frozen_partial_model = set(map(lambda x: f"{x[0]}={x[1]}", filtered_partial_model.items()))

            supersets = self.all_violated_models[int(invert)].supersets(filtered_frozen_partial_model)
            for superset in supersets:
                self.all_violated_models[int(invert)].remove(superset)

            self.all_violated_models[int(invert)].insert(
                filtered_frozen_partial_model, str(counterexample)
            )
            return True, counterexample_names
        else:
            # We can't do anything with this model, so we just return False.
            # subsets = self.inconclusive_models[int(invert)].subsets(frozen_partial_model)
            # for subset in subsets:
            #     self.inconclusive_models[int(invert)].remove(subset)
            self.inconclusive_models[int(invert)].insert(
                frozen_partial_model, str(frozen_partial_model)
            )
            if model == "DTMC":
                self.reasons.append(f"{partial_model} |= {prop}")

            minus_one = 18446744073709551615
            if check_result.consistent_scheduler is not None:
                filtered_partial_model = {self.model_variable_names[i]: x for i, x in enumerate(check_result.consistent_scheduler) if x != minus_one}
                self.all_violated_models[int(not invert)].insert(
                    set(map(lambda x: f"{x[0]}={x[1]}", filtered_partial_model.items())),
                    str(filtered_partial_model),
                )

                return False, check_result.consistent_scheduler
            return False, None
