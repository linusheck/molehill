"""Molehill's core mechanism."""

from settrie import SetTrie
from stormpy import model_checking, CheckTask
from decimal import Decimal
from molehill.fastmole import MatrixGeneratorDouble, MatrixGeneratorRationalNumber
from molehill.counterexamples import check, check_hole_options
from molehill.plugins.search import SearchMarkovChain
from molehill.plugins.split import SplitMarkovChain
import time
import z3
from stormpy import BitVector

class Mole:
    def __init__(
        self,
        solver,
        variables,
        quotient,
        mode="search",
        exact=False,
        draw_image=False,
        considered_counterexamples="all",
    ):
        self.quotient = quotient
        self.exact = exact
        self.mode = mode
        # models we have already analyzed
        self.all_violated_models = [SetTrie(), SetTrie()]
        self.inconclusive_models = [SetTrie(), SetTrie()]

        self.considered_models = 0
        self.mc_calls = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.quotient.build(quotient.family)
        # TODO new choice to assignment?
        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()

        # some states were removed as they were not reachable in the quotient MDP, we need to recompute the choice_to_assignment when this happens
        if len(self.choice_to_assignment) != quotient.family.mdp.model.nr_choices:
            updated_choice_to_assignment = [[] for _ in range(quotient.family.mdp.model.nr_choices)]

            for choice, assignment in enumerate(self.choice_to_assignment):
                if choice not in quotient.family.mdp.quotient_choice_map:
                    continue
                for hole_assignment in assignment:
                    updated_choice_to_assignment[quotient.family.mdp.quotient_choice_map.index(choice)].append(
                        hole_assignment
                    )

            self.choice_to_assignment = updated_choice_to_assignment
        
        print(self.quotient.family)
        print("Family size", "{:.2e}".format(Decimal(self.quotient.family.size)))
        print("Quotient size", self.quotient.family.mdp.model.nr_states)

        # reasons for new assertion
        self.reasons = []

        self.fixed_something = False

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

        if mode == "search":
            self.plugin = SearchMarkovChain(solver, None, self)
        elif mode == "split":
            self.plugin = SplitMarkovChain(solver, None, self)
        else:
            raise ValueError(f"Unknown mode: {mode}")
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
        # result = model_checking(self.quotient.family.mdp.model, prop.formula)
        # global_bounds = result.get_values()

        global_bounds = [0.0 for i in range(self.quotient.family.mdp.model.transition_matrix.nr_columns)]

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
            print(
                f"Considered {self.mc_calls} models so far (cache hits: {self.considered_models - self.mc_calls})"
            )
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

        frozen_partial_model = set(
            map(lambda x: f"{x[0]}={x[1]}", partial_model.items())
        )
        conflicts_violated = list(
            self.all_violated_models[int(invert)].subsets(frozen_partial_model)
        )
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
        conflicts_inverse_violated_sub = self.all_violated_models[
            1 - int(invert)
        ].subsets(frozen_partial_model)
        if len(conflicts_inverse_violated_sub) > 0:
            return False, None
        # And supersets:
        conflicts_inverse_violated_super = self.all_violated_models[
            1 - int(invert)
        ].supersets(frozen_partial_model)
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
        prop = self.quotient.specification
        if invert:
            prop = self.quotient.specification.negate()

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
            counterexample_names = [
                self.model_variable_names[i] for i in counterexample
            ]
            filtered_partial_model = {
                name: partial_model[name] for name in counterexample_names
            }
            filtered_frozen_partial_model = set(
                map(lambda x: f"{x[0]}={x[1]}", filtered_partial_model.items())
            )

            # Push a reason (explain).
            if len(counterexample) < num_fixed:
                self.reasons.append(
                    f"{model} counterexample {num_fixed}->{len(counterexample)} ({partial_model}->{filtered_partial_model})"
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

            supersets = self.all_violated_models[int(invert)].supersets(
                filtered_frozen_partial_model
            )
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
                filtered_partial_model = {
                    self.model_variable_names[i]: x
                    for i, x in enumerate(check_result.consistent_scheduler)
                    if x != minus_one
                }
                self.all_violated_models[int(not invert)].insert(
                    set(
                        map(lambda x: f"{x[0]}={x[1]}", filtered_partial_model.items())
                    ),
                    str(filtered_partial_model),
                )

                return False, check_result.consistent_scheduler
            return False, None

    def hole_options_consistent(self, hole_options, invert=False):
        """Analyze the current sub-MDP and (perhaps) push theory lemmas."""

        if time.time() - self.time_last_print > 1:
            print(
                f"Considered {self.mc_calls} models so far (cache hits: {self.considered_models - self.mc_calls})"
            )
            self.time_last_print = time.time()

        hole_options_bv = []
        for i in range(len(self.variables)):
            bv = BitVector(self.variables[i].size(), 1)
            if self.model_variable_names[i] in hole_options:
                for bit, decision in hole_options[self.model_variable_names[i]].items():
                    if decision == 1:
                        bv.set(bit, False)
            hole_options_bv.append(bv)
        
        # print(self.variables)
        # print([str(x) for x in hole_options_bv])

        # Prop is always rechability, even if our input was until (thanks paynt :)).
        prop = self.quotient.specification
        if invert:
            prop = self.quotient.specification.negate()

        # Check the sub-MDP (see counterexample.py).
        check_result = check_hole_options(
            self.get_matrix_generator(invert),
            hole_options_bv,
            prop,
        )
        self.mc_calls += 1
        all_violated = check_result.all_schedulers_violate
        counterexample = check_result.fixed_holes
        if all_violated:
            counterexample_names = [
                self.model_variable_names[i] for i in counterexample
            ]
            return True, counterexample_names
        else:
            return False, None

    def load_cache(self, cache_file):
        """Load a cache from a file."""
        import pickle
        with open(cache_file, "rb") as f:
            cache = pickle.load(f)
            self.all_violated_models = cache["all_violated_models"]
            self.inconclusive_models = cache["inconclusive_models"]
            print("Cache loaded successfully.")
    
    def dump_cache(self, cache_file):
        """Dump the current cache to a file."""
        import pickle
        cache = {
            "all_violated_models": self.all_violated_models,
            "inconclusive_models": self.inconclusive_models,
        }
        with open(cache_file, "wb") as f:
            pickle.dump(cache, f)
        print("Cache dumped successfully.")

