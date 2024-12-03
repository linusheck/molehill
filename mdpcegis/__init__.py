import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import sys
import time
import math
import matplotlib.pyplot as plt
from PIL import Image

from curve_drawer import add_pixels, new_image

import counterexamples

from model_counters import ModelCounter, ModelEnumeratingPlugin

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
        self.add_decide(self._decide)
        self.add_final(self._final)
        
        # stack of fixed values
        self.fixed_values = []
        # stack of scopes
        self.fixed_count = []
        # the current partial model
        self.partial_model = {}
        # list of Z3 variables, indexed by PAYNT hole
        self.variables = []

        self.considered_models = 0
        # self.ruled_out_models = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()
        state_to_holes_bv = self.quotient.coloring.getStateToHoles().copy()
        self.state_to_holes = []
        for _state, holes_bv in enumerate(state_to_holes_bv):
            holes = set([hole for hole in holes_bv])
            self.state_to_holes.append(holes)

        prop = self.quotient.specification.all_properties()[0]
        # does there exist a model that satisfies the property?
        result = self.quotient.family.mdp.model_check_property(prop.negate())
        self.global_bounds = result.result
        
        self.complete_transition_matrix = self.quotient.family.mdp.model.transition_matrix
        self.decision_matrix = counterexamples.build_decision_matrix(self.complete_transition_matrix, self.global_bounds)

        # run this model counter alongside and feed it all new assertions
        self.model_counter = ModelCounter()
        for a in solver.assertions():
            self.model_counter.solver.add(a)
        
        self.last_decision_variable = None

    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
        self.model_counter.variables = variables

    def push(self):
        self.fixed_count.append(len(self.fixed_values))
        if len(self.fixed_values) == 0 and self.considered_models == 0:
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
        # if str(self.last_decision_variable) == str(ast) or len(self.partial_model) == len(self.variables):
        self.analyse_current_model(ast)
        # otherwise: this is just a propagation, no need to check anything here

    def analyse_current_model(self, last_fixed_var=None):
        # Check model count if it's worth it to check MDP
        # models_in_tree = self.model_counter.count_models(max_models=128, condition=z3.And([key == value for key, value in enumerate(self.partial_model)]))
        # if len(self.partial_model) < len(self.variables):
        #     print(models_in_tree)
        # if len(self.partial_model) < len(self.variables) and models_in_tree < 128:
        #     return

        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variables[hole]
            if var in self.partial_model:
                new_family.hole_set_options(hole, [self.partial_model[var].as_long()])
        self.quotient.build(new_family)

        # e.g. spec is R{"lost"} <= 1 [ F "finished" ]
        # task: find a satisfying assignment
        # questions:
        # - is it the case that the minimal probability is bigger than 1? (this is the case if the spec is unsat)
        # - is it the case that the maximal probability is smaller than 1? (this is the case if the spec is sat)
        mdp = new_family.mdp

        prop = self.quotient.specification.all_properties()[0]
        # does there exist a model that satisfies the property?
        result = mdp.model_check_property(prop)
        # print("Value", result.value)
        self.considered_models += 1

        all_violated = not result.sat

        if all_violated:
            # this DTMC or MDP refutes the spec
            counterexample = counterexamples.compute_counterexample(mdp, result.result, self.variables, self.partial_model, self.state_to_holes, self.choice_to_assignment, prop, self.decision_matrix, self.complete_transition_matrix, self.model_counter)
            if counterexample is not None:
                counterexample_partial_model = {
                    self.variables[c]: self.partial_model[self.variables[c]] for c in counterexample
                }
                print(f"Found counterexample {counterexample_partial_model} while having {len(self.partial_model)} variables fixed: {self.partial_model}")
                term = z3.Not(z3.And([self.variables[c] == counterexample_partial_model[self.variables[c]] for c in counterexample]))
                # print(f"Propagate {term}")
                self.propagate(term, [])
                self.model_counter.solver.add(term)
            else:
                print("No counterexample")
                self.conflict(self.fixed_values)
                self.model_counter.solver.add(z3.Not(z3.And([key == value for key, value in enumerate(self.partial_model)])))
        else:
            if len(self.partial_model) == len(self.variables):
                print(f"Found satisfying DTMC with value {result.value}")
        if time.time() - self.time_last_print > 1:
            print(f"{self.considered_models} MC calls")
            self.time_last_print = time.time()

    def fresh(self, new_ctx):
        pass
        # print("fresh called with new_ctx:", new_ctx)

    def _created(self, e):
        pass

    def _eq(self, e, ids):
        pass
    
    def _decide(self, a, b, c):
        self.last_decision_variable = a
    
    def _final(self):
        pass

def example1(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)
    # print all python properties of quotient
    family = quotient.family

    quotient.build(family)
    s = z3.Solver()

    variables = []
    # create variables
    num_bits = max([math.ceil(math.log2(max(family.hole_options(hole)) + 1)) for hole in range(family.num_holes)]) + 1
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        # TODO hole options of full family should be a sorted vector of indices that is continous
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))
    print(s.assertions())

    # make z3 simple solver
    # make plugin
    p = SearchMarkovChain(s, quotient)
    p.register_variables(variables)
    print(variables)
    # M_0_1=1, M_1_1=3, M_2_1=0, M_3_1=2, P_0_1=2, P_1_1=2, P_2_1=3, P_3_1=2
    # s.add(variables[0] == 3)
    # s.add(variables[2] == 1)
    # s.add(variables[3] == 1)
    # s.add(variables[4] == 2)
    # s.add(variables[5] == 2)
    # s.add(variables[6] == 3)
    # s.add(variables[7] == 2)
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
        print(f"Considered {p.considered_models} models")
    else:
        print("unsat")

    # do this hacky
    return
    
    actual_bits = num_bits - 1
    size = math.ceil(math.sqrt(2**(actual_bits * len(variables))))
    image = new_image(size)
    pixels = image.load()
    new_assertions = p.model_counter.solver.assertions()[len(s.assertions()):]
    N = len(new_assertions)
    images = []
    for j in range(0, N):
        i = int(min(j * (float(len(new_assertions))/N), len(new_assertions)))
        print(i)
        s2 = z3.Solver()
        p2 = ModelEnumeratingPlugin(s2)
        p2.register_variables(variables)

        for a in s.assertions():
            s2.add(a)
        for a in new_assertions[:i]:
            s2.add(a)
        # get all models
        model_numbers = []
        assert s2.check() == z3.unsat
        for m in p2.models:
            variable_values = sum([m[i].as_long() * 2**(i * actual_bits) for i in range(len(variables))])
            model_numbers.append(variable_values)
        color = plt.cm.ocean(float(i) / float(len(new_assertions)))
        ints = tuple([int(255 * x) for x in color])
        add_pixels(pixels, size, model_numbers, ints)
        copied_image = image.copy()
        copied_image = copied_image.resize((size * 10, size * 10), Image.Resampling.NEAREST)
        images.append(copied_image)
    images[0].save("image.gif", save_all=True, append_images=images[1:] + [images[-1].copy()] * 10, duration=100, loop=0)

    image = image.resize((size * 10, size * 10), Image.Resampling.NEAREST)
    image.save("image.png")

if __name__ == "__main__":
    example1(sys.argv[1])
