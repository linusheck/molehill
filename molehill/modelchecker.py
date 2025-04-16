"""Model checking."""

import stormpy.storage
from stormpy.core import parse_properties_without_context
from stormpy import check_model_sparse
from stormpy.pycarl.gmp import Rational
from stormpy import OptimizationDirection


def check_model(mdp, prop, hint, precision=1e-4):
    exact_environment = stormpy.core.Environment()
    exact_environment.solver_environment.minmax_solver_environment.precision = Rational(
        precision
    )
    exact_environment.solver_environment.minmax_solver_environment.method = (
        stormpy.MinMaxMethod.optimistic_value_iteration
    )
    if hint is not None:
        exact_environment.solver_environment.minmax_solver_environment.method = (
            stormpy.MinMaxMethod.topological
        )
    # exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.sound_value_iteration

    # TODO hack (i hate properties)
    # this is okay because we always have reachability properties
    new_prop = parse_properties_without_context(
        str(prop.formula).split()[0] + ' [ F "counterexample_target" ]'
    )[0]

    result = check_model_sparse(
        mdp, new_prop, extract_scheduler=True, hint=hint, environment=exact_environment
    )
    all_schedulers_violate = not prop.satisfies_threshold(
        result.at(mdp.initial_states[0])
    )
    return all_schedulers_violate, result
