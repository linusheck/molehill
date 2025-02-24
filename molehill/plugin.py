"""Z3 plugin for searching MCs."""

import time
import z3
from fastmole import MatrixGenerator
from molehill.model_counters import ModelCounter
from molehill.counterexamples import check

# from molehill.bandit import get_bandit
from stormpy import model_checking, CheckTask
from stormpy.storage import BitVector

class SearchMarkovChain(z3.UserPropagateBase):
    def __init__(
        self,
        solver,
        quotient,
        diseq_info,
        draw_image=False,
        considered_counterexamples="all",
    ):
        super().__init__(solver, None)
        # TODO for some reason the PAYNT quotient MDP has a lot of duplicate rows
        self.quotient = quotient
        self.vars_registered = False
        self.add_fixed(self._fixed)
        # self.add_created(self._created)
        # self.add_eq(self._eq)
        # TODO decide is broken in Z3, do we need it?
        # self.add_decide(self._decide)
        self.add_final(self._final)

        # models we have already analyzed
        self.accepting_models = set()
        self.rejecting_models = set()
        # stack of fixed values
        self.fixed_values = []
        # stack of scopes
        self.fixed_count = []
        # the current partial model
        self.partial_model = {}
        # list of Z3 variables, indexed by PAYNT hole
        self.variables = []
        self.variable_names = []
        self.variable_indices = {}

        self.var_ranges = diseq_info[0]
        self.constant_explanations = diseq_info[1]
        self.disequalities = []

        self.disequality_assignments = None

        self.ast_map = {}

        self.considered_models = 0
        # self.ruled_out_models = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()

        quotient.build(quotient.family)

        prop = self.quotient.specification.all_properties()[0]

        self.check_task = CheckTask(prop.formula)

        # does there exist a model that satisfies the property?
        print("Quotient size", self.quotient.family.mdp.model.nr_states)
        print("Checking quotient")
        result = model_checking(self.quotient.family.mdp.model, prop.formula)
        print("Done")
        self.global_bounds = result.get_values()

        self.complete_transition_matrix = (
            self.quotient.family.mdp.model.transition_matrix
        )
        assert len(self.quotient.family.mdp.model.initial_states) == 1

        # reasons for new assertion
        self.reasons = []

        self.counterexamples = []
        self.diseq_assumptions = []

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

        # target_states == states with target label
        target_states = model_checking(
            self.quotient.family.mdp.model, prop.formula.subformula.subformula
        ).get_truth_values()

        self.matrix_generator = MatrixGenerator(
            self.quotient.family.mdp.model,
            self.check_task,
            target_states,
            self.global_bounds,
            self.choice_to_assignment,
        )

        global_hint_vec = self.global_bounds.copy()
        # extend global hint by two zeros for the two new states in decision matrix
        global_hint_vec.extend([0.0, 0.0])
        self.global_hint = (global_hint_vec, BitVector(len(global_hint_vec), True))

        self.last_decision_variable = None

        self.best_value = 0.0

        self.mdp_fails_and_wins = [0, 0]

        self.draw_image = draw_image
        if self.draw_image:
            self.image_assertions = []
        self.considered_counterexamples = considered_counterexamples

    def register_variables(self, variables, diseq_statements):
        """This method is called once by the user to regigster the variables we
        are going to watch. The diseq_constants are the statements that
        represent all disequalities, e.g., X!=2."""
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
        for var in diseq_statements:
            self.add(var)
        self.variable_names = [str(var) for var in variables]
        self.variable_indices = {var: i for i, var in enumerate(self.variable_names)}
        if self.var_ranges:
            self.disequalities = [
                [
                    BitVector(self.var_ranges[i] + 1, True)
                    for i in range(len(self.variables))
                ]
            ]
            self.disequality_assignments = [[]]

    def push(self):
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
        if self.disequalities:
            self.disequalities.append([BitVector(x) for x in self.disequalities[-1]])
            self.disequality_assignments.append(self.disequality_assignments[-1].copy())

        # Print statement taht shows we are working
        if time.time() - self.time_last_print > 1:
            print("Considered", self.considered_models, "models so far")
            self.time_last_print = time.time()

        # Frozen partial model is hashable :)
        frozen_partial_model = frozenset(self.partial_model.items())
        # If we fixed exactly as many constants as last context, skip this one
        if not (
            len(self.fixed_count) < 2 or self.fixed_count[-1] > self.fixed_count[-2]
        ):
            return

        # Check if we already know this model (Z3 sometimes asks twice)
        if frozen_partial_model in self.rejecting_models:
            # we already know this model rejects
            # we also know this if any model above rejects, which we could check with subsets
            # but this is slow and Z3 doesn't go here in that case
            return
        if frozen_partial_model in self.accepting_models:
            # we already know this model accepts
            return

        measured_time = time.time()
        # Analyze current model and propagate theory lemma
        all_violated, counterexample = self.analyse_current_model()
        measured_time = time.time() - measured_time

        if all_violated:
            self.rejecting_models.add(frozen_partial_model)
            # If we want to draw a nice image, we need this statement
            if self.draw_image:
                self.counterexamples.append(
                    [
                        (
                            self.variable_names[i],
                            self.partial_model[self.variable_names[i]],
                        )
                        for i in counterexample
                    ]
                )
                self.diseq_assumptions.append([BitVector(x) for x in self.disequalities[-1]])
        else:
            self.accepting_models.add(frozen_partial_model)

    def pop(self, num_scopes):
        # This function is called if Z3 pops a context. We keep track of that.
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())
            if self.disequalities:
                self.disequalities.pop()
                self.disequality_assignments.pop()

    def _final(self):
        # This is what is called if Z3 creates a FULL assignment.
        # We basically do the same thing as in push.
        _result, counterexample = self.analyse_current_model()

        # Again, this is for the nice image :)
        if counterexample is not None and self.draw_image:
            self.counterexamples.append(
                [
                    (self.variable_names[i], self.partial_model[self.variable_names[i]])
                    for i in counterexample
                ]
            )
            self.diseq_assumptions.append([BitVector(x) for x in self.disequalities[-1]])

    def get_name_from_ast_map(self, ast):
        """Get name of the AST from the map."""
        # I had to make this function because the Z3 APIs to do the same thing
        # are super slow.
        ast_str = None
        ast_hash = hash(ast)
        if ast_hash in self.ast_map:
            ast_str = self.ast_map[ast_hash]
        else:
            ast_str = ast.decl().name()
            self.ast_map[ast_hash] = ast_str
        return ast_str

    def _fixed(self, ast, value):
        # This is called when Z3 fixes a variable. We need to keep track of that.
        ast_hash = hash(ast)
        if ast_hash in self.constant_explanations:
            explanation = self.constant_explanations[ast_hash]
            # This is a disequality => rule it out in the disequalities bit-vector.
            # print(self.partial_model)
            # print("Disequality", explanation, value)
            # print(explanation[0] in self.partial_model)
            self.disequality_assignments[-1].append(ast)
            if value:
                self.disequalities[-1][self.variable_indices[explanation[0]]].set(
                    int(explanation[1]), False
                )
        else:
            ast_str = self.get_name_from_ast_map(ast)
            self.fixed_values.append(ast_str)
            # This is a model constant => add it to the partial model.
            self.partial_model[ast_str] = value

    def analyse_current_model(self):
        """Analyze the current sub-MDP and (perhaps) push theory lemmas."""
        model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"

        # Make a PAYNT family from the current partial model.
        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variable_names[hole]
            if var in self.partial_model:
                new_family.hole_set_options(hole, [self.partial_model[var].as_long()])

        # Prop is always rechability, even if our input was until (thanks paynt :)).
        prop = self.quotient.specification.all_properties()[0]

        # Decide whether we want to compute a counterexample.
        compute_counterexample = True
        if self.considered_counterexamples == "none":
            compute_counterexample = False
        elif self.considered_counterexamples == "mc" and model == "MDP":
            compute_counterexample = False

        # Check the sub-MDP (see counterexample.py).
        all_violated, counterexample, _result = check(
            self.matrix_generator,
            new_family,
            prop,
            self.disequalities[-1] if self.disequalities else None,
            self.global_hint,
            compute_counterexample,
        )

        self.considered_models += 1

        # Keep track of MDP fails and wins.
        if model == "MDP":
            if all_violated:
                self.mdp_fails_and_wins[1] += 1
            else:
                self.mdp_fails_and_wins[0] += 1

        if all_violated:
            # We found a counterexample, so we need to push a theory lemma.
            conflict = [self.variables[c] for c in counterexample]
            if self.var_ranges:
                for diseq in self.disequality_assignments[-1]:
                    conflict.append(diseq)
            # print(conflict)
            self.conflict(conflict)

            # Push a reason (explain).
            if len(counterexample) < len(self.fixed_values):
                self.reasons.append(
                    f"{model} counterexample {len(self.fixed_values)}->{len(counterexample)}"
                )
            else:
                self.reasons.append(f"{model} reject {len(self.fixed_values)}")

            # If we want to draw a nice image, we need this statement.
            if self.draw_image:
                term = z3.Not(
                    z3.And(
                        [
                            self.variables[c]
                            == self.partial_model[str(self.variables[c])]
                            for c in counterexample
                        ] + self.disequality_assignments[-1]
                    ),
                )
                self.image_assertions.append(term)
                # print(term)
                # print([str(x) for x in self.disequalities[-1]])

            return True, counterexample
        else:
            # We can't do anything with this model, so we just return False.
            return False, None

    def fresh(self, new_ctx):
        # TODO handle fresh contexts from FORALL quantifiers.
        return self
