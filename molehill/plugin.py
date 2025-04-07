"""Z3 plugin for searching MCs."""

import z3


class SearchMarkovChain(z3.UserPropagateBase):
    def __init__(self, solver, ctx, data):
        super().__init__(solver, ctx)
        self.vars_registered = False

        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.add_created(self._created)

        self.data = data
        # stack of fixed values
        self.fixed_values = []
        # stack of scopes
        self.fixed_count = []
        # the current partial model
        self.partial_model = {}

        self.ast_map = {}

        # list of Z3 variables, indexed by PAYNT hole
        self.variables = []
        self.variable_names = []

        self.names_to_vars = {}

        self.function_arguments = {}

        self.child_plugin = None

        self.valid_function = None

    def is_in_ast_map(self, ast):
        return hash(ast) in self.ast_map

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

    def analyse_current_model(self):
        valid_calls = [
            (x, y) for x, y in self.partial_model.items() if isinstance(y, bool)
        ]

        for name, value in valid_calls:
            backwards_variables = {}
            model_for_checker = {}

            involved_variables = self.function_arguments[name]
            for i, var in enumerate(involved_variables):
                var_original = self.data.model_variable_names[i]
                if var in self.partial_model:
                    model_for_checker[var_original] = self.partial_model[var]
                elif var.isdigit():
                    # Suppose the function assignment is something like valid(0)
                    # Then the conflict is just "valid(0)", not "valid(0) and 0=0"
                    model_for_checker[var_original] = int(var)
                backwards_variables[var_original] = var

            # print("Model for checker", model_for_checker)
            all_violated, counterexample = self.data.partial_model_consistent(
                model_for_checker, invert=not value
            )
            if all_violated:
                conflicting_vars = [self.names_to_vars[name]] + [
                    self.names_to_vars[backwards_variables[x]]
                    for x in counterexample
                    if backwards_variables[x] in self.names_to_vars
                ]
                # print("Conflicting vars", conflicting_vars)
                self.conflict(conflicting_vars)
            else:
                if counterexample is None:
                    return
                minus_one = 18446744073709551615
                
                new_vars = []
                quantified_vars = []
                for i, v in enumerate(counterexample):
                    if v != minus_one:
                        # print(i, self.valid_function.arg(i).sort().size())
                        new_vars.append(z3.BitVecVal(int(v), self.valid_function.arg(i).sort().size(), ctx=self.ctx()))
                    else:
                        if involved_variables[i] not in self.names_to_vars:
                            new_vars.append(z3.BitVecVal(int(involved_variables[i]), self.valid_function.arg(i).sort().size(), ctx=self.ctx()))
                        else:
                            new_vars.append(self.names_to_vars[involved_variables[i]])
                            quantified_vars.append(self.names_to_vars[involved_variables[i]])

                if len(quantified_vars) > 0:
                    declaration = z3.ForAll(quantified_vars, self.valid_function.decl()(*new_vars) if value else z3.Not(self.valid_function.decl()(*new_vars)))
                else:
                    declaration = self.valid_function.decl()(*new_vars) if value else z3.Not(self.valid_function.decl()(*new_vars))
                # print(self.solver, self.child_plugin)
                self.propagate(declaration, [])

    def push(self):
        # print(self.partial_model)
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
        if len(self.fixed_count) > 1 and self.fixed_count[-1] == self.fixed_count[-2]:
            return
        # Analyze current model and propagate theory lemma
        self.analyse_current_model()

    def pop(self, num_scopes):
        # This function is called if Z3 pops a context. We keep track of that.
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

    def _final(self):
        # This is what is called if Z3 creates a FULL assignment.
        # We do the same thing as in push.
        self.analyse_current_model()

    def _fixed(self, ast, value):
        # print("Fixed", ast, value)
        # This is called when Z3 fixes a variable. We need to keep track of that.
        if self.is_in_ast_map(ast) or value.sort() != z3.BoolSort():
            ast_str = self.get_name_from_ast_map(ast)
            self.partial_model[ast_str] = value.as_long()
        else:
            ast_str = str(ast)
            self.partial_model[ast_str] = bool(value)
        self.fixed_values.append(ast_str)

    def _created(self, x):
        strx = str(x)
        self.valid_function = x
        self.function_arguments[strx] = []
        self.names_to_vars[strx] = x
        for i in range(x.num_args()):
            argument = x.arg(i)
            if not z3.Z3_is_numeral_ast(x.ctx_ref(), argument.as_ast()):
                self.add(argument)
                name = self.get_name_from_ast_map(argument)
                self.names_to_vars[name] = argument
                # TODO fix this for more complicated expressions than just variables
                self.function_arguments[strx].append(name)
            else:
                self.function_arguments[strx].append(str(argument.as_long()))

    def fresh(self, new_ctx):
        self.child_plugin = SearchMarkovChain(None, new_ctx, self.data)
        return self.child_plugin
