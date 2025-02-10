"""Compute counterexamples."""

from stormpy.storage import BitVector
from stormpy.core import ExplicitModelCheckerHintDouble
from fastmole import hint_convert
from molehill.modelchecker import check_model


def hole_order(bfs_order, choice_to_assignment, possible_holes):
    order = []
    for choice in bfs_order:
        for hole, _ in choice_to_assignment[choice]:
            if hole not in order and hole in possible_holes:
                order.append(hole)
    for hole in possible_holes:
        if hole not in order:
            order.append(hole)
    return order


def check(matrix_generator, choice_to_assignment, family, prop, global_hint=None):
    hole_options = [
        family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
    ]
    fixed_holes = [
        hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
    ]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()
    old_reachable_states = matrix_generator.get_current_reachable_states()
    
    hint_full = None
    if global_hint is not None:
        hint_full = hint_convert(global_hint[0], global_hint[1], old_reachable_states)
    all_schedulers_violate_full, result = check_model(mdp, prop, hint_full)

    if all_schedulers_violate_full:
        bfs_order = matrix_generator.get_current_bfs_order()
        # we abstract in the order of which holes we saw first, which holes we saw second, etc
        abstracted_holes = hole_order(bfs_order, choice_to_assignment, fixed_holes)

        all_schedulers_violate = False
        hint = None
        hint_obj = ExplicitModelCheckerHintDouble()

        # TODO do binary search for the right number of abstracted holes
        while not all_schedulers_violate:
            # try to get an unsat core!!
            # let's start with abstracting all of the nondeterminism into holes
            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes), hole_options
            )
            mdp_holes = matrix_generator.get_current_mdp()

            hint_obj = None
            if hint is not None:
                reachable_states = matrix_generator.get_current_reachable_states()
                hint_obj = hint_convert(hint, old_reachable_states, reachable_states)

            all_schedulers_violate, result = check_model(mdp_holes, prop, hint_obj)
            print(result.get_values()[mdp_holes.initial_states[0]])
            hint = result.get_values()

            if all_schedulers_violate:
                # yaay we have a counterexample!!
                counterexample_holes = [
                    hole for hole in fixed_holes if hole not in abstracted_holes
                ]
                return all_schedulers_violate, counterexample_holes, result
            # abstract fewer holes
            # TODO check if the abstracted hole actually removes nondeterminism
            abstracted_holes = abstracted_holes[1:]
            if len(abstracted_holes) == 0:
                break
            old_reachable_states = matrix_generator.get_current_reachable_states()
    return all_schedulers_violate_full, fixed_holes, result
