"""Z3 plugin for searching MCs."""

import z3
from settrie import SetTrie

class SplitMarkovChain(z3.UserPropagateBase):
    def __init__(self, solver, ctx, data):
        super().__init__(solver, ctx)
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

        self.names_to_vars = {}

        self.function_arguments = {}

        self.child_plugin = None

        self.valid_function = None

        self.policies = {True: [], False: []}

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
            (x, y) for x, y in self.partial_model.items() if isinstance(y, bool) and x.startswith("(valid")
        ]
        for name, value in valid_calls:
            assert value
            for value in [True, False]:
                # print("CHECK")
                # print(self.partial_model)
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
                # print(model_for_checker)
                all_violated, counterexample = self.data.hole_options_consistent(
                    model_for_checker, invert=not value
                )
                # print(counterexample)
                if all_violated:
                    # TODO only do counterexample on true bits, not on false bits

                    conflicting_vars = [self.names_to_vars[name]] + [
                        self.names_to_vars[(backwards_variables[x], i)]
                        for x in counterexample
                        if backwards_variables[x] in self.names_to_vars
                        if backwards_variables[x] in self.partial_model
                        for i in range(self.names_to_vars[backwards_variables[x]].size())
                        if i in self.partial_model[backwards_variables[x]]
                        if self.partial_model[backwards_variables[x]][i]
                    ]
                    # print(counterexample)
                    # print(backwards_variables)
                    # print("Conflicting vars", conflicting_vars)
                    # print(self.names_to_vars)
                    # print(self.partial_model)
                    self.conflict(conflicting_vars)

                    # print("Compute all_blocks")
                    # print(self.partial_model)
                    all_blocks = []
                    for var in counterexample:
                        if not var in self.partial_model:
                            continue
                        for i, bit in self.partial_model[var].items():
                            # print(i, bit)
                            if bit:
                                all_blocks.append((var, i))
                    all_blocks = [x[0] + ";" + str(x[1]) for x in all_blocks]
                    # print("All blocks", all_blocks)
                    # # if len(self.policies[value].subsets(all_blocks)) == 0:
                    # print("insert", all_blocks, value)
                    if not value:
                        self.policies[value].append(all_blocks)
                    break
                else:
                    if counterexample is None:
                        continue
                    assert False  # in the current code, this should never happen

    def push(self):
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
        if len(self.fixed_count) > 1 and self.fixed_count[-1] == self.fixed_count[-2]:
            return
        # Analyze current model and propagate theory lemma
        self.analyse_current_model()
    
    def _final(self):
        # print("final")
        self.analyse_current_model()

    def pop(self, num_scopes):
        # This function is called if Z3 pops a context. We keep track of that.
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                ast_str, pos = self.fixed_values.pop()
                self.partial_model[ast_str].pop(pos, None)

    def _fixed(self, ast, value):
        # print("Fixed", ast, value)
        # This is called when Z3 fixes a variable. We need to keep track of that.
        # if self.is_in_ast_map(ast) or value.sort() != z3.BoolSort():
        if ast.sexpr().startswith("("):
            ast_str = ast.sexpr()
            if ast_str.startswith("(valid"):
                self.partial_model[ast_str] = bool(value)
                self.data.function_argument_tracker.append(
                    [value] + self.function_arguments[ast_str]
                )
                self.fixed_values.append(ast_str)
            else:
                assert ast_str.startswith("((_ bit2bool")
                variable = self.get_name_from_ast_map(ast.children()[0])
                bit = int(ast.decl().params()[0])
                if variable not in self.partial_model:
                    self.partial_model[variable] = {}
                self.partial_model[variable][bit] = bool(value)
                self.fixed_values.append((variable, bit))


        # ast_str = self.get_name_from_ast_map(ast)


    def _created(self, x):
        strx = x.sexpr()
        self.valid_function = x
        self.function_arguments[strx] = []
        self.names_to_vars[strx] = x
        def bit2bool(var, i):
            return z3.BoolRef(z3.Z3_mk_bit2bool(var.ctx.ref(), i, var.as_ast()))
        for i in range(x.num_args()):
            argument = x.arg(i)
            if not z3.Z3_is_numeral_ast(x.ctx_ref(), argument.as_ast()):
                self.add(argument)
                name = self.get_name_from_ast_map(argument)
                self.names_to_vars[name] = argument
                # TODO fix this for more complicated expressions than just variables
                self.function_arguments[strx].append(name)
                bools = [bit2bool(argument, i) for i in range(argument.size())]
                for i, b in enumerate(bools):
                    self.add(b)
                    self.names_to_vars[(name, i)] = b
            else:
                self.function_arguments[strx].append(str(argument.as_long()))

    def fresh(self, new_ctx):
        assert False
