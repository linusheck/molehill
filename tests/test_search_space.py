"""Test matrix generator"""

import pytest
import z3
from stormpy import check_model_sparse, parse_properties_without_context
from stormpy.storage import BitVector
from molehill import run
from molehill.constraints import Constraint

class DummyConstraint(Constraint):
    def build_constraint(self, function, variables):
        return function(*variables)

@pytest.mark.parametrize("project_path", ["resources/test/grid", "resources/test/power", "resources/test/safety", "resources/test/refuel-06-res", "resources/test/herman", "resources/test/maze"])
@pytest.mark.parametrize("considered_counterexamples", ["all", "mc", "none"])
def test_search_space(project_path, considered_counterexamples):
    model, _solver, plugin = run(project_path, False, considered_counterexamples, DummyConstraint(), search_space_test=True)
    # all of our models are unsat, we want to check if we have really considered the whole search space
    assert model is None, "Actual model is SAT: " + str(model)

    print(plugin.counterexamples)

    # check that all rejecting models actually reject
    for i, model in enumerate(plugin.counterexamples):
        model = {x[0]: x[1] for x in model}
        family = plugin.quotient.family.copy()
        family.add_parent_info(plugin.quotient.family)
        for hole in range(family.num_holes):
            var = plugin.model_variable_names[hole]
            if var in model:
                family.hole_set_options(hole, [model[var]])

        hole_options = [
            family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
        ]
        plugin.get_matrix_generator().build_submodel(BitVector(family.num_holes, False), hole_options)

        # Build MDP
        plugin.get_matrix_generator().build_submodel(BitVector(family.num_holes, False), hole_options)
        mdp_nondet = plugin.get_matrix_generator().get_current_mdp()
        prop = plugin.quotient.specification.all_properties()[0]
        new_property = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]
        result_storm_nondet = check_model_sparse(mdp_nondet, new_property)
        all_schedulers_violate = not prop.satisfies_threshold(
            result_storm_nondet.at(mdp_nondet.initial_states[0])
        )
        assert all_schedulers_violate
    # check that plugin.rejecting_models covers the whole search space
    variables = []
    new_solver = z3.Solver()
    family = plugin.quotient.family.copy()
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.Int(name)
        variables.append(var)
        # print(name, options)
        new_solver.add(
            z3.And(
                var >= min(options),
                var <= max(options),
            )
        )
    for i, model in enumerate(plugin.counterexamples):
        model = {x[0]: x[1] for x in model}
        assumption = []
        statement = []
        for hole in range(family.num_holes):
            var = variables[hole]
            if str(var) in model:
                statement.append(var == model[str(var)])
        s = z3.Not(z3.And(*(assumption + statement)))
        new_solver.add(s)
    assert new_solver.check() == z3.unsat, new_solver.model()
