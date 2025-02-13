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


def check(matrix_generator, choice_to_assignment, family, prop, global_hint=None, compute_counterexample=True):
    hole_options = [
        family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
    ]
    fixed_holes = [
        hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
    ]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()
    
    hint_full = None
    # TODO hints are broken!
    #if global_hint is not None:
        #hint_full = hint_convert(global_hint[0], global_hint[1], old_reachable_states)
    all_schedulers_violate_full, result = check_model(mdp, prop, hint_full)

    if all_schedulers_violate_full and compute_counterexample:
        bfs_order = matrix_generator.get_current_bfs_order()
        # we abstract in the order of which holes we saw first, which holes we saw second, etc
        abstracted_holes = hole_order(bfs_order, choice_to_assignment, fixed_holes)

        def check_submodel(ith_hole, abstracted_holes):
            abstracted_holes_here = abstracted_holes[ith_hole:]

            # try to get an unsat core!!
            # let's start with abstracting all of the nondeterminism into holes
            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes_here), hole_options
            )
            mdp_holes = matrix_generator.get_current_mdp()

            # TODO re-implement hint
            # hint_obj = None
            # if hint is not None:
            #     reachable_states = matrix_generator.get_current_reachable_states()
            #     hint_obj = hint_convert(hint, old_reachable_states, reachable_states)

            all_schedulers_violate, result = check_model(mdp_holes, prop, None)
            # print(result.get_values()[mdp_holes.initial_states[0]])
            # hint = result.get_values()

            if all_schedulers_violate:
                # yaay we have a counterexample!!
                counterexample_holes = [
                    hole for hole in fixed_holes if hole not in abstracted_holes_here
                ]
                return all_schedulers_violate, counterexample_holes, result
            # abstract fewer holes
            # old_reachable_states = matrix_generator.get_current_reachable_states()
            return None

        # do a binary search to find the smallest counterexample
        # TODO we don't need to search on the holes that we know are not reachable
        left = 0
        right = len(abstracted_holes)
        while left < right:
            mid = (left + right) // 2
            result = check_submodel(mid, abstracted_holes)
            if result is None:
                left = mid + 1
            else:
                _all_schedulers_violate, fixed_holes, result = result
                right = mid
    return all_schedulers_violate_full, fixed_holes, result
