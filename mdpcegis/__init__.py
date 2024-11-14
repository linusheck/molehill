import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import payntbind.synthesis
import z3
import paynt.parser.sketch
import sys

class Plugin(z3.UserPropagateBase):
    def __init__(self, solver, quotient):
        super().__init__(solver, None)
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

        # initialize counterexample generator
        state_to_holes_bv = self.quotient.coloring.getStateToHoles().copy()
        state_to_holes = []
        for _state, holes_bv in enumerate(state_to_holes_bv):
            holes = set([hole for hole in holes_bv])
            state_to_holes.append(holes)
        formulae = self.quotient.specification.stormpy_formulae()
        self.counterexample_generator = payntbind.synthesis.CounterexampleGeneratorMdp(
            self.quotient.quotient_mdp, self.quotient.family.num_holes, state_to_holes, formulae
        )


    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)

    def push(self):
        # print("push")
        self.fixed_count.append(len(self.fixed_values))

    def pop(self, num_scopes):
        for _scope in range(num_scopes):
            # print("pop")
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

    def _fixed(self, ast, value):
        self.fixed_values.append(ast)
        self.partial_model[ast] = value
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

        prop = self.quotient.specification.all_properties()[0]
        result = new_family.mdp.model_check_property(prop)

        all_violated = not result.sat

        if all_violated:
            # this DTMC or MDP refutes the spec
            self.conflict(self.fixed_values)
        else:
            if len(self.partial_model) == len(self.variables):
                print(f"Found satisfying DTMC with value {result.value}")
                # # check whether this MDP is all-sat
                # prop_negate = self.quotient.specification.negate().all_properties()[0]
                # result_negate = new_family.mdp.model_check_property(prop_negate)

                # all_sat = not result_negate.sat
                # if all_sat:
                #     # we found out with this MDP that this entire subfamily is sat
                #     # just fix all of the rest of the values to zero
                #     assertion = []
                #     for var in self.variables:
                #         if var not in self.partial_model:
                #             assertion.append(var == z3.BitVecVal(0, 32))
                #     self.propagate(z3.And(*assertion, self.solver.ctx), self.fixed_values, [])

    def fresh(self, new_ctx):
        pass
        # print("fresh called with new_ctx:", new_ctx)

    def _created(self, e):
        pass
        # print("_created called with e:", e)

    def _eq(self, e, ids):
        pass
        # print("_eq called with e:", e, "ids:", ids)
    
    def _decide(self, a, b, c):
        pass
        # print("_decide called with", a, b, c)
    
    def _final(self):
        print("_final called with")

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
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, 32)
        variables.append(var)
        # TODO hole options of full family should be a sorted vector of indices that is continous
        s.add(z3.And(var >= z3.BitVecVal(min(options), 32), var <= z3.BitVecVal(max(options), 32)))

    # make z3 simple solver
    # make plugin
    p = Plugin(s, quotient)
    p.register_variables(variables)
    print(s.check())
    model = s.model()

    new_family = quotient.family.copy()
    new_family.add_parent_info(quotient.family)
    for hole in range(new_family.num_holes):
        var = variables[hole]
        new_family.hole_set_options(hole, [model.eval(var).as_long()])
    print(new_family)



if __name__ == "__main__":
    example1(sys.argv[1])
