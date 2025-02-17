"""Z3 plugin for searching MCs."""

import time
import z3
from fastmole import MatrixGenerator
from molehill.model_counters import ModelCounter
from molehill.counterexamples import check
#from molehill.bandit import get_bandit
from stormpy import model_checking, CheckTask
from stormpy.storage import BitVector
from copy import deepcopy

class SearchMarkovChain(z3.UserPropagateBase):
    def __init__(self, solver, quotient, diseq_info, draw_image=False, considered_counterexamples="all"):
        super().__init__(solver, None)
        # TODO for some reason the PAYNT quotient MDP has a lot of duplicate rows
        self.quotient = quotient
        self.vars_registered = False
        self.add_fixed(self._fixed)
        # self.add_created(self._created)
        self.add_eq(self._eq)
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
        result = model_checking(
            self.quotient.family.mdp.model, prop.formula
        )
        print("Done")
        self.global_bounds = result.get_values()

        self.complete_transition_matrix = (
            self.quotient.family.mdp.model.transition_matrix
        )
        assert len(self.quotient.family.mdp.model.initial_states) == 1

        # run this model counter alongside and feed it all new assertions
        self.model_counter = ModelCounter()
        for a in solver.assertions():
            self.model_counter.solver.add(a)

        # reasons for new assertion
        self.reasons = []

        self.counterexamples = []

        self.fixed_something = False
        
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

        # get type of MatrixGenerator constructor
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
        
        # self.bandit = get_bandit()

    def register_variables(self, variables, diseq_constants):
        # print("register", variables)
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
        for var in diseq_constants:
            self.add(var)
        self.model_counter.variables = variables
        self.variable_names = [str(var) for var in variables]
        self.variable_indices = {var: i for i, var in enumerate(self.variable_names)}
        if self.var_ranges:
            self.disequalities = [
                [BitVector(self.var_ranges[i] + 1, True) for i in range(len(self.variables))]
            ]

    def push(self):
        self.fixed_count.append(len(self.fixed_values))
        if self.disequalities:
            self.disequalities.append([BitVector(x) for x in self.disequalities[-1]])
        if time.time() - self.time_last_print > 1:
            print("Considered", self.considered_models, "models so far")
            self.time_last_print = time.time()
        frozen_partial_model = frozenset(self.partial_model.items())

        if not (
            len(self.fixed_count) < 2 or self.fixed_count[-1] > self.fixed_count[-2]
        ):
            return

        if frozen_partial_model in self.rejecting_models:
            # we already know this model rejects
            # we also know this if any model above rejects, which we could check with subsets
            # but this is slow and Z3 doesn't go here in that case
            return
        if frozen_partial_model in self.accepting_models:
            # we already know this model accepts
            return

        # models_below = len(self.variables) - len(self.fixed_values)

        # action = self.bandit.pull()
        # if action[0] == 1:
        #     self.bandit.update([0])
        #     return

        measured_time = time.time()
        # counterexample is already propagated to the solver inside of this
        # function, we don't need it
        all_violated, counterexample = self.analyse_current_model()
        measured_time = time.time() - measured_time

        if all_violated:
            self.rejecting_models.add(frozen_partial_model)
            if self.draw_image:
                self.counterexamples.append([(self.variable_names[i], self.partial_model[self.variable_names[i]]) for i in counterexample])
            # self.bandit.update([models_below])
        else:
            self.accepting_models.add(frozen_partial_model)
            # self.bandit.update([-models_below])

    def pop(self, num_scopes):
        for _scope in range(num_scopes):
            # print("pop")
            last_count = self.fixed_count.pop()
            # remove all variables from partial_model
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())
            if self.disequalities:
                self.disequalities.pop()


    def get_name_from_ast_map(self, ast):
        ast_str = None
        ast_hash = hash(ast)
        if ast_hash in self.ast_map:
            ast_str = self.ast_map[ast_hash]
        else:
            ast_str = ast.decl().name()
            self.ast_map[ast_hash] = ast_str
        return ast_str

    def _fixed(self, ast, value):
        ast_hash = hash(ast)
        if ast_hash in self.constant_explanations:
            explanation = self.constant_explanations[ast_hash]
            # this is an inferred disequality
            if value:
                self.disequalities[-1][self.variable_indices[explanation[0]]].set(int(explanation[1]), False)
        else:
            ast_str = self.get_name_from_ast_map(ast)
            self.fixed_values.append(ast_str)
            # this is a model variable
            self.partial_model[ast_str] = value
        # otherwise: this is just a propagation, no need to check anything here

    def analyse_current_model(self):
        model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"

        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variable_names[hole]
            if var in self.partial_model:
                new_family.hole_set_options(hole, [self.partial_model[var].as_long()])

        prop = self.quotient.specification.all_properties()[0]
        # prop is always rechability, even if our input was until (thanks paynt :))

        model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"
        compute_counterexample = True
        if self.considered_counterexamples == "none":
            compute_counterexample = False
        elif self.considered_counterexamples == "mc" and model == "MDP":
            compute_counterexample = False

        all_violated, counterexample, _result = check(
            self.matrix_generator, self.choice_to_assignment, new_family, prop, self.disequalities[-1] if self.disequalities else None, self.global_hint, compute_counterexample
        )

        self.considered_models += 1

        if model == "MDP":
            if all_violated:
                self.mdp_fails_and_wins[1] += 1
            else:
                self.mdp_fails_and_wins[0] += 1

        if all_violated:
            #print(len(self.fixed_values), "->", len(counterexample))
            self.conflict([self.variables[c] for c in counterexample])
            if self.draw_image:
                term = z3.Not(
                    z3.And(
                        [
                            self.variables[c]
                            == self.partial_model[str(self.variables[c])]
                            for c in counterexample
                        ]
                    )
                )
                self.image_assertions.append(term)
            # self.model_counter.solver.add(term)

            if len(counterexample) < len(self.fixed_values):
                self.reasons.append(
                    f"{model} counterexample {len(self.fixed_values)}->{len(counterexample)}"
                )
            else:
                self.reasons.append(f"{model} reject {len(self.fixed_values)}")
            return True, counterexample
        else:
            return False, None

    def fresh(self, new_ctx):
        return self

    # def _created(self, e):
    #     print("Created", e)
    #     pass

    def _eq(self, e, ids):
        # print("eq", e, ids)
        pass

    # def _decide(self, a, b, c):
    #     print("decide", a, b, c)

    # def _diseq(self, a, b):
    #     a_str = self.get_name_from_ast_map(a)
    #     b_str = self.get_name_from_ast_map(b)
    #     self.diseqs[-1].append((a_str, b_str))

    def _final(self):
        # print("final -> analyse current model", self.partial_model)
        _result, counterexample = self.analyse_current_model()
        if counterexample is not None and self.draw_image:
            self.counterexamples.append([(self.variable_names[i], self.partial_model[self.variable_names[i]]) for i in counterexample])
