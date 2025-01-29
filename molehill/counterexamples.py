"""Compute counterexamples."""

from stormpy import check_model_sparse, model_checking, parse_properties_without_context, get_reachable_states
from stormpy.storage import BitVector
import stormpy.storage
import stormpy.core
from fastmole import hint_convert
from pycarl.gmp import Rational

def _check_model(mdp, prop, hint):
    exact_environment = stormpy.core.Environment()
    exact_environment.solver_environment.minmax_solver_environment.precision = Rational(1e-6)
    exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.optimistic_value_iteration
    # exact_environment.solver_environment.minmax_solver_environment.method = stormpy.MinMaxMethod.sound_value_iteration

    # TODO hack (i hate properties)
    new_prop = parse_properties_without_context(str(prop.formula).split()[0] + " [ F \"counterexample_target\" ]")[0]

    result = check_model_sparse(mdp, new_prop, extract_scheduler=True, hint=hint, environment=exact_environment)
    all_schedulers_violate = not prop.satisfies_threshold(result.at(mdp.initial_states[0]))

    return all_schedulers_violate, result

def hole_order(bfs_order, choice_to_assignment, possible_holes):
    order = []
    for choice in bfs_order:
        for hole, _ in choice_to_assignment[choice]:
            if hole not in order and hole in possible_holes:
                order.append(hole)
    return order

def check(matrix_generator, choice_to_assignment, family, prop):
    hole_options = [family.family.holeOptionsMask(hole) for hole in range(family.num_holes)]
    fixed_holes = [hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()
    all_schedulers_violate_full, result = _check_model(mdp, prop, None)
    if all_schedulers_violate_full:
        # always keep track of the previous reachable states
        old_reachable_states = matrix_generator.get_current_reachable_states()

        bfs_order = matrix_generator.get_current_bfs_order()
        # we abstract in the order of which holes we saw first, which holes we saw second, etc
        abstracted_holes = hole_order(bfs_order, choice_to_assignment, fixed_holes)
        # print(abstracted_holes)
        # abstracted_holes = [0, 3, 6, 2, 5, 4, 1]
        all_schedulers_violate = False
        while not all_schedulers_violate:
            # try to get an unsat core!!
            # let's start with abstracting all of the nondeterminism into holes
            matrix_generator.build_submodel(BitVector(family.num_holes, abstracted_holes), hole_options)
            mdp_holes = matrix_generator.get_current_mdp()
            hint = hint_convert(result.get_values(), old_reachable_states, matrix_generator.get_current_reachable_states())
            all_schedulers_violate, result = _check_model(mdp_holes, prop, hint)
            # print(abstracted_holes, result.get_values()[mdp_holes.initial_states[0]], prop, all_schedulers_violate)
            if all_schedulers_violate:
                # yaay we have a counterexample!!
                counterexample_holes = [hole for hole in fixed_holes if hole not in abstracted_holes]
                # print("Counterexample found", counterexample_holes, family)
                return all_schedulers_violate, counterexample_holes, result
            # abstract fewer holes
            ## TODO this might be useful - recompute order?
            # new_bfs_order = matrix_generator.get_current_bfs_order()
            # abstracted_holes = hole_order(new_bfs_order, choice_to_assignment, abstracted_holes)
            abstracted_holes = abstracted_holes[1:]
            if len(abstracted_holes) == 0:
                break
            old_reachable_states = matrix_generator.get_current_reachable_states()
    return all_schedulers_violate_full, fixed_holes, result
