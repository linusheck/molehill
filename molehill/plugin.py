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
        var_ranges,
        track_disequalities,
        draw_image=False,
        considered_counterexamples="all",
    ):
        super().__init__(solver, None)
        self.quotient = quotient

        self.vars_registered = False

        self.var_ranges = var_ranges
        self.track_disequalities = track_disequalities

        self.add_fixed(self._fixed)
        self.add_final(self._final)

        # self.add_created(self._created)

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

        self.disequalities = []
        self.disequality_assignments = None
        self.disequality_variables = None
        self.disequality_explanations = None

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
        result = model_checking(self.quotient.family.mdp.model, prop.formula)
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


    def update_disequalities_from_assignments(self):
        # disequality assignments are a list of decisions about the bitvectors:
        # [ // hole 1: [(0, False), (1, True), (2, False), ...]
        #   // hole 2: [(0, False), (1, True), (2, False), ...]
        # ]
        # we need to update the bitvectors, that reference the numbers accordingly
        for assignment in self.disequality_assignments[-1]:
            var_index, bit, value, _i = assignment
            # print("Update", var_index, bit, value)
            for i in range(self.disequalities[-1][var_index].size()):
                if (i & (1 << bit)) >> bit != int(value):
                    self.disequalities[-1][var_index].set(i, False)
                    # print("We know", self.variable_names[var_index], "is not", i)

    def register_variables(self, variables):
        """This method is called once by the user to regigster the variables we
        are going to watch. The diseq_constants are the statements that
        represent all disequalities, e.g., X!=2."""
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)

        self.variable_names = [self.get_name_from_ast_map(var) for var in variables]
        self.variable_indices = {var: i for i, var in enumerate(self.variable_names)}

        if self.track_disequalities:
            self.disequalities = [
                [
                    BitVector(self.var_ranges[i] + 1, True)
                    for i in range(len(self.variables))
                ]
            ]
            self.disequality_assignments = [[]]
            self.disequality_variables = [[]]
            self.disequality_explanations = {}
            for hole, var in enumerate(self.variables):
                num_bits = var.size()
                def bit2bool(var, i):
                    return z3.BoolRef(z3.Z3_mk_bit2bool(var.ctx.ref(), i, var.as_ast()))

                for i in range(num_bits):
                    bit2bool_var = bit2bool(var, i)
                    self.add(bit2bool_var)
                    # explain this bit
                    self.disequality_explanations[hash(bit2bool_var)] = (hole, i)
                    # print("Explain", bit2bool_var, self.disequality_explanations[hash(bit2bool_var)])

    def push(self):
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
        if self.disequalities:
            self.disequalities.append([BitVector(x) for x in self.disequalities[-1]])
            self.disequality_assignments.append(self.disequality_assignments[-1].copy())
            self.disequality_variables.append(self.disequality_variables[-1].copy())

        # Print statement taht shows we are working
        if time.time() - self.time_last_print > 1:
            print("Considered", self.considered_models, "models so far")
            self.time_last_print = time.time()

        def make_frozen_partial_model():
            # Frozen partial model is hashable :)
            return frozenset(self.partial_model.items())
        frozen_partial_model = make_frozen_partial_model()
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
                if self.track_disequalities:
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
                self.disequality_variables.pop()
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
            if self.track_disequalities:
                self.diseq_assumptions.append([BitVector(x) for x in self.disequalities[-1]])


    def _fixed(self, ast, value):
        # print("Fixed", ast, value)
        # This is called when Z3 fixes a variable. We need to keep track of that.
        ast_hash = hash(ast)
        if self.track_disequalities and ast_hash in self.disequality_explanations:
            explanation = self.disequality_explanations[ast_hash]
            # This is a disequality => rule it out in the disequalities bit-vector.
            # print(self.partial_model)
            # print("Disequality", explanation, value)
            # print(explanation[0] in self.partial_model)
            index_of_diseq_variable = len(self.disequality_variables[-1])
            self.disequality_variables[-1].append(ast)
            self.disequality_assignments[-1].append((explanation[0], explanation[1], bool(value), index_of_diseq_variable))
            # print(self.disequality_variables)
            # print(self.disequality_assignments)
            self.update_disequalities_from_assignments()   
        else:
            ast_str = self.get_name_from_ast_map(ast)
            self.fixed_values.append(ast_str)
            # This is a model constant => add it to the partial model.
            self.partial_model[ast_str] = value.as_long()

    def analyse_current_model(self):
        """Analyze the current sub-MDP and (perhaps) push theory lemmas."""
        model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"

        # Make a PAYNT family from the current partial model.
        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variable_names[hole]
            if var in self.partial_model:
                new_family.hole_set_options(hole, [self.partial_model[var]])

        # Prop is always rechability, even if our input was until (thanks paynt :)).
        prop = self.quotient.specification.all_properties()[0]

        # Decide whether we want to compute a counterexample.
        compute_counterexample = True
        if self.considered_counterexamples == "none":
            compute_counterexample = False
        elif self.considered_counterexamples == "mc" and model == "MDP":
            compute_counterexample = False

        # Check the sub-MDP (see counterexample.py).
        check_result = check(
            self.matrix_generator,
            new_family,
            prop,
            self.disequalities[-1] if self.disequalities else None,
            self.global_hint,
            compute_counterexample,
        )
        all_violated = check_result.all_schedulers_violate
        counterexample = check_result.fixed_holes
        nondet_holes = check_result.nondet_holes

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
            # print(self.partial_model)
            if self.track_disequalities:
                conflict.extend([self.disequality_variables[-1][diseq[3]] for diseq in self.disequality_assignments[-1] if diseq[0] in nondet_holes])
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
                if self.track_disequalities:
                    diseqs = [self.disequality_variables[-1][diseq[3]] for diseq in self.disequality_assignments[-1] if diseq[0] in nondet_holes]
                else:
                    diseqs = []
                term = z3.Not(
                    z3.And(
                        [
                            self.variables[c]
                            == self.partial_model[str(self.variables[c])]
                            for c in counterexample
                        ] + diseqs
                    ),
                )
                self.image_assertions.append(term)
            return True, counterexample
        else:
            # We can't do anything with this model, so we just return False.
            return False, None

    def fresh(self, new_ctx):
        # TODO handle fresh contexts from FORALL quantifiers.
        return self
    
    # def _decide(self, x, y, z):
    #     print("Decide", x, y, z)
