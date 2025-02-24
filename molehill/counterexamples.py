"""Compute counterexamples."""

from stormpy.storage import BitVector
from fastmole import hint_convert, intersect_bitvectors
from molehill.modelchecker import check_model


def check(
    matrix_generator,
    family,
    prop,
    disequalities,
    global_hint=None,
    compute_counterexample=True,
):
    # These are the options for each hole.
    hole_options = [
        family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
    ]
    if disequalities:
        # If we keep track of disequalities, we need to intersect the options.
        hole_options = [
            intersect_bitvectors(a, b) for a, b in zip(hole_options, disequalities)
        ]
        # TODO Should we make sure that there are still options left?
        # There should always be options left, idk, but Z3 might give us an empty set??
        # if any([len(list(x)) == 0 for x in hole_options]):
        #     print("does this happen?")
        #     return True, fixed_holes, None
    # These are the holes that are fixed to a single value.
    fixed_holes = [
        hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
    ]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()

    all_schedulers_violate_full, result = check_model(mdp, prop, None)
    if not all_schedulers_violate_full:
        # if matrix_generator.is_scheduler_consistent(result.scheduler):
        #     # TODO we should return the scheduler here (currently just printing it)
        #     # print("Found consistent scheduler")
        return False, None, result

    # The CEs currently get abstracted in BFS order.
    bfs_order = matrix_generator.get_current_bfs_order()
    reachable_hole_order, append_these = matrix_generator.hole_order(
        bfs_order, set(fixed_holes)
    )

    # Only holes that are reachable are interesting for the CE core. We can
    # immediately "delete" the other ones.
    fixed_holes = reachable_hole_order

    if all_schedulers_violate_full and compute_counterexample:
        # We abstract in the order of which holes we saw first, which holes we saw second, etc...

        def check_ce_candidate(ith_hole, abstracted_holes, hint=None):
            abstracted_holes_here = (abstracted_holes + append_these)[ith_hole:]

            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes_here), hole_options
            )
            mdp_holes = matrix_generator.get_current_mdp()

            # TODO hints are broken
            # hint_obj = None
            # if hint is not None:
            #     hint_values = hint[0]
            #     old_reachable_states = hint[1]
            #     reachable_states = matrix_generator.get_current_reachable_states()
            #     hint_obj = hint_convert(
            #         hint_values, old_reachable_states, reachable_states
            #     )

            all_schedulers_violate, result = check_model(mdp_holes, prop, None)
            # print(result.get_values()[mdp_holes.initial_states[0]])
            # hint = result.get_values()

            if all_schedulers_violate:
                # Counterexample found
                counterexample_holes = [
                    hole for hole in fixed_holes if hole not in abstracted_holes_here
                ]
                return all_schedulers_violate, counterexample_holes, result
            else:
                # Not a counterexample
                return False, None, result

        # first, check the weakest counterexample candidate
        weakest_ce_result = check_ce_candidate(
            len(reachable_hole_order) - 1, reachable_hole_order
        )
        if weakest_ce_result[0]:
            # Do a binary search to find the smallest counterexample
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
    return True, fixed_holes, result
