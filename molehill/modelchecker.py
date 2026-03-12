"""Model checking."""

import stormpy
from stormpy import parse_properties_without_context
from stormpy import check_model_sparse
from stormpy.pycarl.gmp import Rational
from molehill.fastmole import set_max_iterations
import os
import payntbind.synthesis
import paynt.verification.property


def check_model(mdp, prop, hint, precision=1e-6):
    environment = stormpy.Environment()
    environment.solver_environment.minmax_solver_environment.precision = Rational(
        precision
    )
    environment.solver_environment.minmax_solver_environment.method = (
        stormpy.MinMaxMethod.optimistic_value_iteration
    )

    if os.getenv("POLICY_ITERATION", "0") == "1":
        environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.policy_iteration

    if hint is not None:
        environment.solver_environment.minmax_solver_environment.method = (
            stormpy.MinMaxMethod.topological
        )
    # environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.sound_value_iteration

    set_max_iterations(
        environment.solver_environment.minmax_solver_environment, 10_000
    )

    # assert that prop.formula is a reachability property
    assert prop.formula.subformula.is_eventually_formula

    # print(f"Checking model of type {type(mdp)}")

    if isinstance(mdp, stormpy.SparseSmg):
        # this is okay because we always have reachability properties because PAYNT gives us them
        new_prop = parse_properties_without_context(
            "<<0>>" + str(prop).split()[0] + ' [ F "counterexample_target" ]'
        )[0]

        # results = []
        # for i in range(10):
        #     # make a paynt property from new_prop
        #     print(new_prop.raw_formula)

        paynt.verification.property.Property.initialize()
        result = payntbind.synthesis.model_check_smg(mdp, new_prop.raw_formula, env=paynt.verification.property.Property.environment)
            # results.append(result)
        # check that all results are the same
        # for i in range(1, len(results)):
        #     for s in mdp.states:
        #         assert results[0].at(s) == results[i].at(s), f"Results differ at state {s}: {results[0].at(s)} vs {results[i].at(s)}"

    else:
        # this is okay because we always have reachability properties because PAYNT gives us them
        new_prop = parse_properties_without_context(
            str(prop).split()[0] + ' [ F "counterexample_target" ]'
        )[0]

        result = check_model_sparse(
            mdp, new_prop, extract_scheduler=False, hint=hint, environment=environment
        )

    all_schedulers_violate = result.at(mdp.initial_states[0])
    return all_schedulers_violate, result
