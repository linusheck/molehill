"""Model checking."""

import stormpy
from stormpy.core import parse_properties_without_context
from stormpy import check_model_sparse
from stormpy.pycarl.gmp import Rational
from fastmole import set_max_iterations
import os

def check_model(mdp, prop, hint, precision=1e-6):
    environment = stormpy.core.Environment()
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

    # this is okay because we always have reachability properties because PAYNT gives us them
    new_prop = parse_properties_without_context(
        str(prop).split()[0] + ' [ F "counterexample_target" ]'
    )[0]

    result = check_model_sparse(
        mdp, new_prop, extract_scheduler=False, hint=hint, environment=environment
    )
    all_schedulers_violate = result.at(mdp.initial_states[0])
    return all_schedulers_violate, result
