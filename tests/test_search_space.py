"""Test matrix generator"""

import pytest
import z3
from stormpy import check_model_sparse, parse_properties_without_context
from stormpy.storage import BitVector
from molehill import run
from fastmole import intersect_bitvectors

@pytest.mark.parametrize("project_path", ["resources/test/grid", "resources/test/power", "resources/test/safety", "resources/test/refuel-06-res", "resources/test/herman", "resources/test/maze"])
@pytest.mark.parametrize("considered_counterexamples", ["all", "mc", "none"])
# @pytest.mark.parametrize("diseq", [False, True])
@pytest.mark.parametrize("diseq", [False])
def test_search_space(project_path, considered_counterexamples, diseq):
    def custom_solver_settings(s):
        s.set(unsat_core=True)
    model, _solver, plugin = run(project_path, False, considered_counterexamples, custom_solver_settings, search_space_test=True, track_disequalities=diseq)
    # all of our models are unsat, we want to check if we have really considered the whole search space
    assert model is None

    # check that all rejecting models actually reject
    for i, model in enumerate(plugin.counterexamples):
        model = {x[0]: x[1] for x in model}
        family = plugin.quotient.family.copy()
        family.add_parent_info(plugin.quotient.family)
        for hole in range(family.num_holes):
            var = plugin.variable_names[hole]
            if var in model:
                family.hole_set_options(hole, [model[var]])

        hole_options = [
            family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
        ]
        if diseq:
            hole_options = [
                intersect_bitvectors(a, b) for a, b in zip(hole_options, plugin.diseq_assumptions[i])
            ]
        # print(plugin.diseq_assumptions[i])
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
        if diseq:
            diseq_assumptions = plugin.diseq_assumptions[i]
            for hole in range(family.num_holes):
                assumptions = diseq_assumptions[hole]
                var = variables[hole]
                for x in range(len(assumptions)):
                    if not assumptions[x]:
                        assumption.append(var != x)
        statement = []
        for hole in range(family.num_holes):
            var = variables[hole]
            if str(var) in model:
                statement.append(var == model[str(var)])
        s = z3.Not(z3.And(*(assumption + statement)))
        new_solver.add(s)
    assert new_solver.check() == z3.unsat, new_solver.model()
