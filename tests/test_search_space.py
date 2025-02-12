"""Test matrix generator"""

import pytest
from paynt.parser.sketch import Sketch
from molehill.plugin import SearchMarkovChain
from molehill.counterexamples import hole_order
import z3
from stormpy import check_model_sparse, parse_properties_without_context
from stormpy.storage import BitVector
from molehill import run
from functools import reduce

@pytest.mark.parametrize("project_path", ["resources/test/grid", "resources/test/power", "resources/test/safety", "resources/test/refuel-06-res", "resources/test/herman"])
def test_search_space(project_path):
    def custom_solver_settings(s):
        s.set(unsat_core=True)
    model, _solver, plugin = run(project_path, False, custom_solver_settings)
    # all of our models are unsat, we want to check if we have really considered the whole search space
    assert model is None

    # check that all rejecting models actually reject
    for model in plugin.rejecting_models:
        model = {x[0]: x[1] for x in model}
        family = plugin.quotient.family.copy()
        family.add_parent_info(plugin.quotient.family)
        for hole in range(family.num_holes):
            var = plugin.variable_names[hole]
            if var in model:
                family.hole_set_options(hole, [model[var].as_long()])

        hole_options = [
            family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
        ]
        plugin.matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)

        # Build MDP
        plugin.matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
        mdp_nondet = plugin.matrix_generator.get_current_mdp()
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
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.Int(name)
        variables.append(var)
        new_solver.add(
            z3.And(
                var >= min(options),
                var <= max(options),
            )
        )
    print(plugin.rejecting_models)
    for model in plugin.rejecting_models:
        model = {x[0]: x[1].as_long() for x in model}
        for hole in range(family.num_holes):
            var = variables[hole]
            if str(var) in model:
                new_solver.add(var != model[str(var)])
    assert new_solver.check() == z3.unsat
