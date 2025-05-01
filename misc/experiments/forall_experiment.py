import z3


class ForallPropagator(z3.UserPropagateBase):
    def __init__(self, solver):
        super().__init__(solver, None)
        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.add_created(self._created)

        self.vars_registered = False
        self.solver = solver
        self.variables = []
        self.variable_names = []

        self.names_to_vars = {}

        # stack of fixed values
        self.fixed_values = []
        # stack of scopes
        self.fixed_count = []
        # the current partial model
        self.partial_model = {}

    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
            self.variable_names.append(str(var))
            self.names_to_vars[str(var)] = var

    def analyse_current_model(self):
        # find all valid calls in the partial model
        valid_calls = [
            (x, bool(y)) for x, y in self.partial_model.items() if x.startswith("valid")
        ]
        # valid(x!1, y!0, 0)
        # involved variables: [x!1, y!0]

        for name, value in valid_calls:
            partial_model_here = {}
            involved_variables = name.split("(")[1][:-1].split(", ")
            actual_variables = []
            for i, var in enumerate(involved_variables):
                var_original = str(self.variables[i])
                if var in self.partial_model:
                    partial_model_here[var_original] = self.partial_model[var]
                    actual_variables.append(self.names_to_vars[var])
                elif var.isdigit():
                    partial_model_here[var_original] = int(var)
            print(involved_variables)
            print(self.variables)
            print(valid_calls)
            print("partial model", self.partial_model)
            print("partial model here", partial_model_here)
            print("expecting result", value)

            model_consistent, counterexample = self.partial_model_consistent(
                partial_model_here
            )

            if model_consistent != value:
                print("Conflict", [self.names_to_vars[str(x)] for x in counterexample])
                self.conflict([self.names_to_vars[str(x)] for x in counterexample])

    def partial_model_consistent(self, partial_model):
        print(partial_model)
        if "z" in partial_model and partial_model["z"] == 0:
            return False, partial_model.keys()
        return True, partial_model.keys()

    def push(self):
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
        self.analyse_current_model()

    def pop(self, num_scopes):
        # This function is called if Z3 pops a context. We keep track of that.
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

    def _fixed(self, ast, value):
        print("Fixed", ast, value)
        self.fixed_values.append(str(ast))
        # This is a model constant => add it to the partial model.
        self.partial_model[str(ast)] = value
        print(self.partial_model)

    def fresh(self, new_ctx):
        print("Fresh")
        return self

    def _created(self, x):
        print("Created", x)
        print(dir(x))
        print(x.sort())
        for i in range(x.num_args()):
            argument = x.arg(i)
            print("Watch", argument)
            self.add(argument)
            if not z3.Z3_is_numeral_ast(x.ctx_ref(), argument.as_ast()):
                self.add(argument)
                self.names_to_vars[str(argument)] = argument
                print("Add", argument)

    def _final(self):
        print("Final")
        self.analyse_current_model()
        return


def test_forall():
    s = z3.Solver()
    x = z3.BitVec("x", 1)
    y = z3.BitVec("y", 1)
    z = z3.BitVec("z", 1)
    f = z3.PropagateFunction(
        "valid", z3.BitVecSort(1), z3.BitVecSort(1), z3.BitVecSort(1), z3.BoolSort()
    )
    s.add(z3.ForAll([y, z], f(x, y, z)))
    # s.add(f(x,y,z))
    s.add(x == 1)
    s.add(y == 2)
    s.add(z == 3)
    propagator = ForallPropagator(s)
    propagator.register_variables([x, y, z])
    print(s.check())
    print(s.model())


if __name__ == "__main__":
    test_forall()
