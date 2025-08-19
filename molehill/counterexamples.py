"""Compute counterexamples."""

from stormpy.storage import BitVector
from molehill.modelchecker import check_model
from dataclasses import dataclass


@dataclass
class CECheckResult:
    all_schedulers_violate: bool
    fixed_holes: list
    nondet_holes: list
    result: any
    consistent_scheduler: any = None


def check(
    matrix_generator,
    family,
    spec,
    compute_counterexample=True,
    remove_optimal_holes=True,
):
    prop = spec.negate().all_properties()[0]
    # These are the options for each hole.
    hole_options = [
        family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
    ]
    # These are the holes that are fixed to a single value.
    fixed_holes = [
        hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
    ]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()

    all_schedulers_violate_full, result = check_model(mdp, prop, None)
    if not all_schedulers_violate_full:
        # Optionally, we can check if the scheduler is consistent (not implemented).
        # sched_consistent_result = matrix_generator.is_scheduler_consistent(result.scheduler)
        # if sched_consistent_result is not None:
        #     return CECheckResult(False, None, None, result, sched_consistent_result)
        return CECheckResult(False, None, None, result)

    # The CEs currently get abstracted in BFS order.
    bfs_order = matrix_generator.get_current_bfs_order()
    reachable_hole_order, append_these = matrix_generator.hole_order(
        bfs_order, set(range(family.num_holes))
    )

    # Only holes that are reachable are interesting for the CE core. We can
    # immediately "delete" the other ones.
    fixed_holes = [hole for hole in fixed_holes if hole in reachable_hole_order]
    # Every hole that is not fixed is currently abstracted by MDP.
    holes_as_mdp = [hole for hole in reachable_hole_order if hole not in fixed_holes]

    if remove_optimal_holes:
        assert False, "Not tested."
        append_these = [hole for hole in append_these if hole in reachable_hole_order]
        optimization_direction = prop.formula.optimality_type
        optimal_holes = matrix_generator.optimal_assignments(
            result.scheduler, result.get_values(), optimization_direction
        )
        for h in optimal_holes:
            if h in fixed_holes:
                fixed_holes.remove(h)

    if all_schedulers_violate_full and compute_counterexample:
        assert False, "Not tested."
        # We abstract in the order of which holes we saw first, which holes we saw second, etc...

        def check_ce_candidate(ith_hole, abstracted_holes, hint=None):
            abstracted_holes_here = (abstracted_holes + append_these)[ith_hole:]

            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes_here), hole_options
            )
            mdp_holes = matrix_generator.get_current_mdp()

            all_schedulers_violate, result = check_model(mdp_holes, prop, None)

            if all_schedulers_violate:
                # Counterexample found
                counterexample_holes = [
                    hole for hole in fixed_holes if hole not in abstracted_holes_here
                ]
                return CECheckResult(
                    all_schedulers_violate, counterexample_holes, None, result
                )
            else:
                # Not a counterexample
                return CECheckResult(all_schedulers_violate, None, None, result)

        # first, check the weakest counterexample candidate
        weakest_ce_result = check_ce_candidate(
            len(reachable_hole_order) - 1, reachable_hole_order
        )
        if weakest_ce_result.all_schedulers_violate:
            # Do a binary search to find the smallest counterexample
            left = 1
            right = len(reachable_hole_order) - 2
            num_steps = 0
            while left < right:
                num_steps += 1
                mid = (left + right) // 2
                check_result = check_ce_candidate(mid, reachable_hole_order, None)
                if not check_result.all_schedulers_violate:
                    result = check_result.result
                    left = mid + 1
                else:
                    fixed_holes = check_result.fixed_holes
                    result = check_result.result
                    right = mid

    # Even if we do not compute a counterexample, we can use the knowledge that
    # some holes are unreachable. The statement is only about the reachable holes,
    # so we get a "core" without any further work.
    return CECheckResult(all_schedulers_violate_full, fixed_holes, holes_as_mdp, result)


def check_hole_options(
    matrix_generator,
    hole_options,
    spec,
):
    prop = spec.negate().all_properties()[0]
    num_holes = len(hole_options)
    # These are the options for each hole.
    matrix_generator.build_submodel(BitVector(num_holes, False), hole_options)
    mdp = matrix_generator.get_current_mdp()

    all_schedulers_violate_full, result = check_model(mdp, prop, None)
    if not all_schedulers_violate_full:
        # Optionally, we can check if the scheduler is consistent (not implemented).
        # sched_consistent_result = matrix_generator.is_scheduler_consistent(result.scheduler)
        # if sched_consistent_result is not None:
        #     return CECheckResult(False, None, None, result, sched_consistent_result)
        return CECheckResult(False, None, None, result)

    # The CEs currently get abstracted in BFS order.
    bfs_order = matrix_generator.get_current_bfs_order()
    reachable_hole_order, _append_these = matrix_generator.hole_order(
        bfs_order, set(range(num_holes))
    )

    # Only holes that are reachable are interesting for the CE core. We can
    # immediately "delete" the other ones.
    fixed_holes = [hole for hole in range(len(hole_options)) if hole in reachable_hole_order]
    holes_as_mdp = None

    # Even if we do not compute a counterexample, we can use the knowledge that
    # some holes are unreachable. The statement is only about the reachable holes,
    # so we get a "core" without any further work.
    return CECheckResult(all_schedulers_violate_full, fixed_holes, holes_as_mdp, result)
