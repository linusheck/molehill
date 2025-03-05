"""Z3 plugin for searching MCs."""

import time
import z3
from fastmole import MatrixGenerator
from molehill.model_counters import ModelCounter
from molehill.counterexamples import check

# from molehill.bandit import get_bandit
from stormpy import model_checking, CheckTask

class SearchMarkovChain(z3.UserPropagateBase):
    def __init__(
        self,
        solver,
        quotient,
        var_ranges,
        draw_image=False,
        considered_counterexamples="all",
    ):
        super().__init__(solver, None)
        self.quotient = quotient

        self.vars_registered = False

        self.var_ranges = var_ranges

        self.add_fixed(self._fixed)
        self.add_final(self._final)
        self.add_created(self._created)

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
        
        self.names_to_vars = {}

        self.function_arguments = {}

        self.ast_map = {}

        self.considered_models = 0
        # self.ruled_out_models = 0
        self.total_models = self.quotient.family.size

        self.time_last_print = time.time()

        self.choice_to_assignment = self.quotient.coloring.getChoiceToAssignment()

        quotient.build(quotient.family)


        # reasons for new assertion
        self.reasons = []

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

        self.complete_transition_matrix = (
            self.quotient.family.mdp.model.transition_matrix
        )
        assert len(self.quotient.family.mdp.model.initial_states) == 1

        # target_states == states with target label
        self.matrix_generators = {}

        self.mdp_fails_and_wins = [0, 0]

        self.draw_image = draw_image
        if self.draw_image:
            self.image_assertions = []
        self.considered_counterexamples = considered_counterexamples
        self.counterexamples = []

    def get_matrix_generator(self, invert=False):
        if invert in self.matrix_generators:
            return self.matrix_generators[invert]
        spec = self.quotient.specification
        if invert:
            spec = spec.negate()
        prop = spec.all_properties()[0]
        check_task = CheckTask(prop.formula)

        # does there exist a model that satisfies the property?
        print("Quotient size", self.quotient.family.mdp.model.nr_states)
        result = model_checking(self.quotient.family.mdp.model, prop.formula)
        global_bounds = result.get_values()

        target_states = model_checking(
            self.quotient.family.mdp.model, prop.formula.subformula.subformula
        ).get_truth_values()

        generator = MatrixGenerator(
            self.quotient.family.mdp.model,
            check_task,
            target_states,
            global_bounds,
            self.choice_to_assignment,
        )
        print(generator)
        self.matrix_generators[invert] = generator
        return generator

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

    def register_variables(self, variables):
        """This method is called once by the user to regigster the variables we
        are going to watch."""
        assert not self.vars_registered
        self.vars_registered = True
        for var in variables:
            self.add(var)
            self.variables.append(var)
            self.names_to_vars[self.get_name_from_ast_map(var)] = var
        self.variable_names = [self.get_name_from_ast_map(var) for var in variables]

    def push(self):
        """This method is called if Z3 pushes a new context. This is where we check the sub-MDP."""
        # Keep track of the new context
        self.fixed_count.append(len(self.fixed_values))
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
        else:
            self.accepting_models.add(frozen_partial_model)

    def pop(self, num_scopes):
        # This function is called if Z3 pops a context. We keep track of that.
        for _scope in range(num_scopes):
            last_count = self.fixed_count.pop()
            while len(self.fixed_values) > last_count:
                self.partial_model.pop(self.fixed_values.pop())

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

    def _fixed(self, ast, value):
        # This is called when Z3 fixes a variable. We need to keep track of that.
        if value.sort() == z3.BoolSort():
            ast_str = str(ast)
            self.partial_model[ast_str] = bool(value)
        else:
            ast_str = self.get_name_from_ast_map(ast)
            self.partial_model[ast_str] = value.as_long()
        self.fixed_values.append(ast_str)
    
    def analyse_current_model(self):
        valid_calls = [(x, y) for x, y in self.partial_model.items() if isinstance(y, bool)]

        overall_model_consistent = True

        backwards_variables = {}

        for name, value in valid_calls:
            print(name, value)
            partial_model_here = {}
            involved_variables = self.function_arguments[name]
            for i, var in enumerate(involved_variables):
                var_original = self.variable_names[i]
                if var in self.partial_model:
                    partial_model_here[var_original] = self.partial_model[var]
                elif var.isdigit():
                    # Suppose the function assignment is something like valid(0)
                    # Then the conflict is just "valid(0)", not "valid(0) and 0=0"
                    partial_model_here[var_original] = int(var)
                backwards_variables[var_original] = var

            all_violated, counterexample = self.partial_model_consistent(partial_model_here, invert=not value)
            print(all_violated)
            print(self.variable_names, involved_variables)
            print(backwards_variables)

            if all_violated:
                conflicting_vars = [self.names_to_vars[backwards_variables[x]] for x in counterexample if backwards_variables[x] in self.names_to_vars]
                self.conflict([self.names_to_vars[name]] + conflicting_vars)

                if self.draw_image:
                    self.counterexamples.append(
                        [
                            (
                                backwards_variables[i],
                                self.partial_model[backwards_variables[i]],
                            )
                            for i in counterexample
                        ]
                    )

            overall_model_consistent = overall_model_consistent and not all_violated

        return overall_model_consistent, None

    def partial_model_consistent(self, partial_model, invert=False):
        """Analyze the current sub-MDP and (perhaps) push theory lemmas."""

        num_fixed = len(partial_model.keys())
        model = "DTMC" if num_fixed == len(self.variables) else "MDP"

        # Make a PAYNT family from the current partial model.
        new_family = self.quotient.family.copy()
        new_family.add_parent_info(self.quotient.family)
        for hole in range(new_family.num_holes):
            var = self.variable_names[hole]
            if var in partial_model:
                new_family.hole_set_options(hole, [partial_model[var]])

        # Prop is always rechability, even if our input was until (thanks paynt :)).
        prop = self.quotient.specification.all_properties()[0]
        if invert:
            print("Inverting property", prop)
            prop = self.quotient.specification.negate().all_properties()[0]
            print("Inverted property", prop)

        # Decide whether we want to compute a counterexample.
        compute_counterexample = True
        if self.considered_counterexamples == "none":
            compute_counterexample = False
        elif self.considered_counterexamples == "mc" and model == "MDP":
            compute_counterexample = False
        
        # Check the sub-MDP (see counterexample.py).
        check_result = check(
            self.get_matrix_generator(invert),
            new_family,
            prop,
            compute_counterexample,
        )
        all_violated = check_result.all_schedulers_violate
        counterexample = check_result.fixed_holes

        self.considered_models += 1

        # Keep track of MDP fails and wins.
        if model == "MDP":
            if all_violated:
                self.mdp_fails_and_wins[1] += 1
            else:
                self.mdp_fails_and_wins[0] += 1
        if all_violated:
            # Push a reason (explain).
            if len(counterexample) < num_fixed:
                self.reasons.append(
                    f"{model} counterexample {num_fixed}->{len(counterexample)}"
                )
            else:
                self.reasons.append(f"{model} reject {num_fixed}")

            # If we want to draw a nice image, we need this statement.
            if self.draw_image:
                term = z3.Not(
                    z3.And(
                        [
                            self.variables[c]
                            == partial_model[str(self.variables[c])]
                            for c in counterexample
                        ]
                    ),
                )
                self.image_assertions.append(term)
            return True, [self.variable_names[i] for i in counterexample]
        else:
            # We can't do anything with this model, so we just return False.
            return False, None

    def _created(self, x):
        print("Created", x)
        print(dir(x))
        print(x.sort())
        strx = str(x)
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
        print("Fresh")
        return self
    
    # def _decide(self, x, y, z):
    #     print("Decide", x, y, z)
