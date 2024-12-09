import z3

class ModelEnumeratingPlugin(z3.UserPropagateBase):
    """Z3 plugin that enumerates all models."""
    def __init__(self, solver):
        super().__init__(solver, None)
        self.vars_registered = False
        self.models = set()
        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.fixed_values = []
        self.fixed_count = []
        self.variables = []
        self.partial_model = {}

    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)

    def push(self):
        self.fixed_count.append(len(self.fixed_values))

    def pop(self, num_scopes):
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

    def _fixed(self, ast, value):
        self.fixed_values.append(ast)
        self.partial_model[ast] = value

    def _final(self):
        if len(self.fixed_values) == len(self.variables):
            self.models.add(tuple(sorted(list(self.partial_model.items()), key=lambda x: str(x[0]))))
            self.conflict(self.fixed_values)

class ModelCountingPlugin(z3.UserPropagateBase):
    """Z3 plugin that counts the number of models. Used by remaining_models."""
    def __init__(self, solver, max_models = None):
        super().__init__(solver, None)
        self.vars_registered = False
        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.reset(max_models=max_models)
    
    def reset(self, max_models = None):
        self.models = []
        self.fixed_values = []
        self.fixed_count = []
        self.variables = []
        self.num_models = 0
        self.max_models = max_models

    def register_variables(self, variables):
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)

    def push(self):
        self.fixed_count.append(len(self.fixed_values))

    def pop(self, num_scopes):
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.fixed_values.pop()

    def _fixed(self, ast, value):
        self.fixed_values.append(ast)

    def _final(self):
        if len(self.fixed_values) == len(self.variables):
            self.num_models += 1
            if self.max_models is None or self.num_models < self.max_models:
                self.conflict(self.fixed_values)

class ModelCounter:
    """Holds a Z3 solver that counts the number of models."""
    def __init__(self):
        self.solver = z3.Solver()
        # this gets set when variables are registered
        self.variables = None

    def count_models(self, max_models = None, condition = None):
        """Count the number of models of a solver."""
        assertions = self.solver.assertions()
        self.solver.reset()
        mc = ModelCountingPlugin(self.solver, max_models)
        mc.register_variables(self.variables)
        for a in assertions:
            self.solver.add(a)
        self.solver.push()
        if condition is not None:
            self.solver.add(condition)
        self.solver.check()
        self.solver.pop()
        if max_models is not None:
            return min(mc.num_models, max_models)
        return mc.num_models

    def is_sat(self, condition):
        """Check if a condition is satisfiable."""
        assertions = self.solver.assertions()
        self.solver.reset()
        for a in assertions:
            self.solver.add(a)
        self.solver.push()
        self.solver.add(condition)
        result = self.solver.check()
        self.solver.pop()
        return result == z3.sat
