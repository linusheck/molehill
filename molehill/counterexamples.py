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
    opponent_holes=None,
):
    # These are the options for each hole.
    hole_options = [
        family.family.holeOptionsMask(hole) for hole in range(family.num_holes)
    ]
    # These are the holes that are fixed to a single value.
    fixed_holes = [
        hole for hole in range(family.num_holes) if len(family.hole_options(hole)) <= 1
    ]
    matrix_generator.build_submodel(BitVector(family.num_holes, False), hole_options, opponent_holes=opponent_holes)
    if opponent_holes is not None:
        mdp = matrix_generator.get_current_smg()
        prop = spec.all_properties()[0]
        all_schedulers_violate_full, result = check_model(mdp, prop, None)
        all_schedulers_violate_full = not all_schedulers_violate_full
    else:
        mdp = matrix_generator.get_current_mdp()
        prop = spec.negate().all_properties()[0]
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
    if opponent_holes is not None:
        fixed_holes.extend(opponent_holes)

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
        # Repeatedly abstract fixed holes until no further local generalization is possible.
        def check_ce_candidate(candidate_fixed_holes):
            candidate_fixed_holes = set(candidate_fixed_holes)
            abstracted_holes_here = [
                hole for hole in reachable_hole_order if hole not in candidate_fixed_holes
            ] + append_these

            matrix_generator.build_submodel(
                BitVector(family.num_holes, abstracted_holes_here),
                hole_options,
                opponent_holes=opponent_holes,
            )
            if opponent_holes is not None:
                mdp_holes = matrix_generator.get_current_smg()
            else:
                mdp_holes = matrix_generator.get_current_mdp()

            all_schedulers_violate, check_result = check_model(mdp_holes, prop, None)
            if opponent_holes is not None:
                all_schedulers_violate = not all_schedulers_violate

            if all_schedulers_violate:
                counterexample_holes = [
                    hole for hole in fixed_holes if hole in candidate_fixed_holes
                ]
                return CECheckResult(
                    all_schedulers_violate, counterexample_holes, None, check_result
                )
            return CECheckResult(all_schedulers_violate, None, None, check_result)

        fixed_holes = list(fixed_holes)
        while True:
            removed_hole = False
            for hole in list(fixed_holes):
                candidate_fixed_holes = [h for h in fixed_holes if h != hole]
                check_result = check_ce_candidate(candidate_fixed_holes)
                result = check_result.result
                if check_result.all_schedulers_violate:
                    fixed_holes = check_result.fixed_holes
                    removed_hole = True
                    break
            if not removed_hole:
                break

    # Every hole that is not fixed is currently abstracted by MDP.
    holes_as_mdp = [hole for hole in reachable_hole_order if hole not in fixed_holes]

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
