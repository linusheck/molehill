"""Compute counterexamples."""

from stormpy.storage import BitVector
from stormpy.core import ExplicitModelCheckerHintDouble
from fastmole import hint_convert, hole_order
from molehill.modelchecker import check_model

def hole_order_old(bfs_order, choice_to_assignment, possible_holes):
    order = []
    for choice in bfs_order:
        for hole, _ in choice_to_assignment[choice]:
            if hole not in order and hole in possible_holes:
                order.append(hole)
    append_these = []
    for hole in possible_holes:
        if hole not in order:
            append_these.append(hole)
    return order, append_these


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
    reachable_full = matrix_generator.get_current_reachable_states()

    bfs_order = matrix_generator.get_current_bfs_order()
    reachable_hole_order, append_these = hole_order(bfs_order, choice_to_assignment, set(fixed_holes))

    # Essentially, only holes that are reachable are interesting
    fixed_holes = reachable_hole_order

    if all_schedulers_violate_full and compute_counterexample:
        # we abstract in the order of which holes we saw first, which holes we saw second, etc
        # print(abstracted_holes, append_these)

        def check_ce_candidate(ith_hole, abstracted_holes, hint=None):
            abstracted_holes_here = (abstracted_holes + append_these)[ith_hole:]

            # try to get an unsat core!!
            # let's start with abstracting all of the nondeterminism into holes
            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes_here), hole_options
            )
            mdp_holes = matrix_generator.get_current_mdp()

            hint_obj = None
            if hint is not None:
                hint_values = hint[0]
                old_reachable_states = hint[1]
                reachable_states = matrix_generator.get_current_reachable_states()
                hint_obj = hint_convert(hint_values, old_reachable_states, reachable_states)

            all_schedulers_violate, result = check_model(mdp_holes, prop, hint_obj)
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
            return False, None, result

        # first, check the weakest counterexample candidate
        weakest_ce_result = check_ce_candidate(len(reachable_hole_order) - 1, reachable_hole_order)
        reachable = reachable_full
        if weakest_ce_result[0]:
            # do a binary search to find the smallest counterexample
            # TODO we don't need to search on the holes that we know are not reachable
            left = 1
            right = len(reachable_hole_order) - 2
            num_steps = 0
            while left < right:
                num_steps += 1
                mid = (left + right) // 2
                check_result = check_ce_candidate(mid, reachable_hole_order, None)
                # check_result = check_ce_candidate(mid, abstracted_holes, (result.get_values(), matrix_generator.get_current_reachable_states()))
                if not check_result[0]:
                    _, _, result = check_result
                    left = mid + 1
                else:
                    _all_schedulers_violate, fixed_holes, result = check_result
                    right = mid
            # print(f"Found counterexample with {len(fixed_holes)} holes, originally {len(reachable_hole_order)} with {len(append_these)} additional, in {num_steps} steps")

    # Even if we do not compute a counterexample, we can use the knowledge that
    # some holes are unreachable. The statement is only about the reachable holes,
    # so we get a "core" without any further work.
    return all_schedulers_violate_full, fixed_holes, result
