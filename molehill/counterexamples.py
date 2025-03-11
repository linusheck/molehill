"""Compute counterexamples."""

from stormpy.storage import BitVector
from fastmole import intersect_bitvectors
from molehill.modelchecker import check_model
from dataclasses import dataclass


@dataclass
class CECheckResult:
    all_schedulers_violate: bool
    fixed_holes: list
    nondet_holes: list
    result: any


def analyze_scheduler(
        result,
        matrix_generator,
        family,
        mole,
        fixed_holes,
        prop
):
    scheduler = result.scheduler
    values = result.get_values()
    # print("Analyzing scheduler", scheduler)
    reachable_states = matrix_generator.get_current_reachable_states()
    holes_optimal = BitVector(family.num_holes, True)
    prop_str = str(prop)
    matrix = mole.complete_transition_matrix
    for sub_state, global_state in enumerate(reachable_states):
        row_group_start = matrix.get_row_group_start(global_state)
        row_group_end = matrix.get_row_group_end(global_state)
        if row_group_end == row_group_start + 1:
            continue
        for row in range(row_group_start, row_group_end):
            print(mole.choice_to_assignment[global_state], row_group_start - row_group_end)
            hole, value = mole.choice_to_assignment[global_state][row - row_group_start]
            # TODO this is wrong because the scheduler MIGHT be on a row that is not fully there
            if (row - row_group_start) == scheduler.get_choice(sub_state):
                continue
            value_here = 0.0
            for entry in matrix.get_row(row):
                value_here += entry.value() * mole.global_bounds[False][entry.column]
            # print(value_here, resulting_prob, prop_str)
            assert "<=" in prop_str or ">=" in prop_str
            if "<=" in prop_str and value_here <= resulting_prob:
                holes_optimal.set(hole, False)
                break
            if ">=" in prop_str and value_here >= resulting_prob:
                holes_optimal.set(hole, False)
                break


            if hole not in fixed_holes or not holes_optimal.get(hole):
                continue
            chosen_value = scheduler.get_choice(sub_state)
            resulting_prob = values[sub_state]

    print(fixed_holes, holes_optimal)

def check(
    matrix_generator,
    family,
    prop,
    mole,
    compute_counterexample=True,
):
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
        # if matrix_generator.is_scheduler_consistent(result.scheduler):
        #     # TODO we should return the scheduler here (currently just printing it)
        #     # print("Found consistent scheduler")
        return CECheckResult(False, None, None, result)

    # The CEs currently get abstracted in BFS order.
    bfs_order = matrix_generator.get_current_bfs_order()
    # reachable_hole_order, append_these = matrix_generator.hole_order(
    #     bfs_order, set(fixed_holes)
    # )
    reachable_hole_order, append_these = matrix_generator.hole_order(
        bfs_order, set(range(family.num_holes))
    )

    # Only holes that are reachable are interesting for the CE core. We can
    # immediately "delete" the other ones.
    fixed_holes = [hole for hole in fixed_holes if hole in reachable_hole_order]
    append_these = [hole for hole in append_these if hole in reachable_hole_order]
    # Every hole that is not fixed is currently abstracted by MDP.
    holes_as_mdp = [hole for hole in reachable_hole_order if hole not in fixed_holes]

    analyze_scheduler(result, matrix_generator, family, mole, fixed_holes, prop)

    if all_schedulers_violate_full and compute_counterexample:
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
