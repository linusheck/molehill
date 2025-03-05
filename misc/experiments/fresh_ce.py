import z3

class ForallPropagator(z3.UserPropagateBase):
    def __init__(self, solver, ctx=None):
        super().__init__(solver, ctx)
        print("Create init")
        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.add_created(self._created)
        self.child_propagator = None
        self.vars_registered = False
        self.variables = []
        self.variable_names = []

    # def register_variables(self, variables):
    #     assert not self.vars_registered
    #     self.vars_registered = True
    #     for var in variables:
    #         self.add(var)
    #         self.variables.append(var)
    #         self.variable_names.append(str(var))
    
    def push(self):
        pass

    def pop(self, num_scopes):
        pass

    def _fixed(self, ast, value):
        print("Fixed", ast, value)
        pass

    def fresh(self, new_ctx):
        print("Fresh")
        self.child_propagator = ForallPropagator(None, ctx=new_ctx)
        return self.child_propagator

    def _created(self, x):
        print("Created", x)
        print(dir(x))
        print(x.sort())
        print("Current solver", self.solver)
        for i in range(x.num_args()):
            argument = x.arg(i)
            print("Add", argument)
            if not z3.Z3_is_numeral_ast(x.ctx_ref(), argument.as_ast()):
                self.add(argument)
                print("Add", argument)
    
    def _final(self):
        pass


def test_forall():
    s = z3.Solver()
    x = z3.BitVec("x", 1)
    y = z3.BitVec("y", 1)
    z = z3.BitVec("z", 1)
    f = z3.PropagateFunction("valid", z3.BitVecSort(1), z3.BitVecSort(1), z3.BitVecSort(1), z3.BoolSort())
    s.add(z3.ForAll([y,z], f(x, y, z)))
    # s.add(f(x,y,z))
    s.add(x == 1)
    s.add(y == 2)
    s.add(z == 3)
    propagator = ForallPropagator(s)
    print("Register")
    # propagator.register_variables([x, y, z])
    print("Check")
    print(s.check())
    print(s.model())

if __name__ == "__main__":
    test_forall()
