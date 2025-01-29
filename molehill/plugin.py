"""Z3 plugin for searching MCs."""

import time
import z3
from fastmole import MatrixGenerator
from molehill.model_counters import ModelCounter
from molehill.counterexamples import check
from stormpy import model_checking

class SearchMarkovChain(z3.UserPropagateBase):
    def __init__(self, solver, quotient):
        super().__init__(solver, None)
        # TODO for some reason the PAYNT quotient MDP has a lot of duplicate rows
        self.quotient = quotient
        self.vars_registered = False
        self.add_fixed(self._fixed)
        self.add_created(self._created)
        self.add_eq(self._eq)
        # TODO decide is broken in Z3, do we need it?
        self.decide = None
        self.add_final(self._final)
        
        # stack of fixed values
        self.fixed_values = []
        # stack of scopes
        self.fixed_count = []
        # the current partial model
        self.partial_model = {}
        # list of Z3 variables, indexed by PAYNT hole
        self.variables = []

        # keep a set of analysed models
        self.analysed_models = set()

        self.considered_models = 0
        # self.ruled_out_models = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()

        quotient.build(quotient.family)

        prop = self.quotient.specification.all_properties()[0]
        # open("whole_mdp.dot", "w").write(self.quotient.family.mdp.model.to_dot())
        # does there exist a model that satisfies the property?
        result = self.quotient.family.mdp.model_check_property(prop)
        self.global_bounds = result.result.get_values()
        
        self.complete_transition_matrix = self.quotient.family.mdp.model.transition_matrix
        assert len(self.quotient.family.mdp.model.initial_states) == 1

        # run this model counter alongside and feed it all new assertions
        self.model_counter = ModelCounter()
        for a in solver.assertions():
            self.model_counter.solver.add(a)
        
        # reasons for new assertion
        self.reasons = []

        self.fixed_something = False

        # TODO make this call general
        target_state = model_checking(self.quotient.family.mdp.model, prop.formula.subformula.subformula).get_truth_values()

        # get type of MatrixGenerator constructor
        self.matrix_generator = MatrixGenerator(self.quotient.family.mdp.model, target_state, self.global_bounds, self.choice_to_assignment)
        
        self.last_decision_variable = None

        self.best_value = 0.0
    
    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
        self.model_counter.variables = variables

    def push(self):
        self.fixed_count.append(len(self.fixed_values))
        # print("PUSH", self.fixed_count)
        # print("push -> analyse current model", self.partial_model)
        model_as_list = tuple([self.partial_model[var] if var in self.partial_model else None for var in self.variables])
        if model_as_list in self.analysed_models:
            return
        self.analysed_models.add(model_as_list)
        if len(self.fixed_count) < 2 or self.fixed_count[-1] > self.fixed_count[-2]:
            self.analyse_current_model()

    def pop(self, num_scopes):
        for _scope in range(num_scopes):
            # print("pop")
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

    def _fixed(self, ast, value):
        self.fixed_values.append(ast)
        self.partial_model[ast] = value
        # otherwise: this is just a propagation, no need to check anything here

    def analyse_current_model(self, last_fixed_var=None):
        # print("Analyse current model", self.partial_model)
        # # Check model count if it's worth it to check MDP
        # if len(self.partial_model) < len(self.variables):
        #     models_in_tree = self.model_counter.count_models(max_models=16, condition=z3.And([key == value for key, value in self.partial_model.items()]))
        #     # if len(self.partial_model) < len(self.variables):
        #     #     print("models in tree", models_in_tree)
        #     if len(self.partial_model) < len(self.variables) and models_in_tree < 16:
        #         return
        model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"
        # if model == "MDP":
        #     return

        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variables[hole]
            if var in self.partial_model:
                new_family.hole_set_options(hole, [self.partial_model[var].as_long()])

        prop = self.quotient.specification.all_properties()[0]
        all_violated, counterexample, result = check(self.matrix_generator, self.choice_to_assignment, new_family, prop)

        self.considered_models += 1

        if all_violated:
            counterexample_partial_model = {
                self.variables[c]: self.partial_model[self.variables[c]] for c in counterexample
            }
            # print(f"Found counterexample {counterexample_partial_model} while having {len(self.partial_model)} variables fixed: {self.partial_model}")
            term = z3.Not(z3.And([self.variables[c] == counterexample_partial_model[self.variables[c]] for c in counterexample]))
            # print(f"Propagate {term}")
            # self.propagate(term, [])
            self.conflict([self.variables[c] for c in counterexample])
            self.model_counter.solver.add(term)

            model = "DTMC" if len(self.fixed_values) == len(self.variables) else "MDP"
            if len(counterexample) < len(self.fixed_values):
                self.reasons.append(f"{model} counterexample {len(self.fixed_values)}->{len(counterexample)}")
            else:
                self.reasons.append(f"{model} reject {len(self.fixed_values)}")

    def fresh(self, new_ctx):
        pass
        # print("fresh called with new_ctx:", new_ctx)

    def _created(self, e):
        pass

    def _eq(self, e, ids):
        pass
    
    # def _decide(self, a, b, c):
    #     self.last_decision_variable = a
    
    def _final(self):
        # print("final -> analyse current model", self.partial_model)
        self.analyse_current_model()
