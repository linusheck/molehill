from datetime import time

import molehill
from molehill.constraints import ExistsConstraint
import click
import argparse

import paynt
from multiprocessing import Process, Queue

from queue import Empty

from stormpy import CheckTask, model_checking
from molehill.fastmole import MatrixGeneratorDouble

from stormpy.storage import BitVector

from molehill.modelchecker import check_model

from dataclasses import dataclass

def get_matrix_generator(quotient):
    spec = quotient.specification
    spec = spec.negate()
    prop = spec.all_properties()[0]
    check_task = CheckTask(prop.formula)

    result = model_checking(quotient.family.mdp.model, prop.formula)
    global_bounds = result.get_values()

    target_states = model_checking(
        quotient.family.mdp.model, prop.formula.subformula.subformula
    ).get_truth_values()
    generator = MatrixGeneratorDouble(
        quotient.family.mdp.model,
        check_task,
        target_states,
        global_bounds,
        quotient.coloring.getChoiceToAssignment()
    )
    return generator



@dataclass
class CECheckResult:
    all_schedulers_violate: bool
    fixed_holes: list
    nondet_holes: list
    result: any
    consistent_scheduler: any = None

def get_counterexample_cores(family, quotient, matrix_generator):
    spec = quotient.specification

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
    prop = spec.all_properties()[0]
    all_schedulers_violate_full, result = check_model(mdp, prop, None)

    if not all_schedulers_violate_full:
        print("The property is not satisfied??", result.at(0))

    # The CEs currently get abstracted in BFS order.
    bfs_order = matrix_generator.get_current_bfs_order()
    reachable_hole_order, append_these = matrix_generator.hole_order(
        bfs_order, set(range(family.num_holes))
    )

    # Only holes that are reachable are interesting for the CE core. We can
    # immediately "delete" the other ones.
    fixed_holes = [hole for hole in fixed_holes if hole in reachable_hole_order]

    # Repeatedly abstract fixed holes until no further local generalization is possible.
    def check_ce_candidate(candidate_fixed_holes):
        candidate_fixed_holes = set(candidate_fixed_holes)
        abstracted_holes_here = [
            hole for hole in reachable_hole_order if hole not in candidate_fixed_holes
        ] + append_these

        matrix_generator.build_submodel(
            BitVector(family.num_holes, abstracted_holes_here), hole_options
        )
        mdp_holes = matrix_generator.get_current_mdp()

        all_schedulers_violate, result = check_model(mdp_holes, prop, None)

        if all_schedulers_violate:
            # Counterexample found
            counterexample_holes = [
                hole for hole in fixed_holes if hole in candidate_fixed_holes
            ]
            return CECheckResult(
                all_schedulers_violate, counterexample_holes, None, result
            )
        # Not a counterexample
        return CECheckResult(all_schedulers_violate, None, None, result)

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
    # Create family with a locally minimal counterexample core.
    new_family = quotient.family.copy()
    for hole in fixed_holes:
        new_family.hole_set_options(hole, hole_options[hole])
    # Also create an action-to-label dict
    cause_dict = {}
    for hole in fixed_holes:
        hole_name = quotient.family.hole_name(hole)
        assert len(family.hole_options(hole)) == 1
        hole_option = family.hole_options(hole)[0]
        cause_dict[hole_name] = quotient.family.hole_to_option_labels[hole][hole_option]
    return new_family, cause_dict

def process_conflict(partial_model, quotient, matrix_generator):
    # Make a PAYNT family from the current partial model.
    new_family = quotient.family.copy()
    new_family.add_parent_info(quotient.family)

    model_variable_names = [quotient.family.hole_name(hole) for hole in range(new_family.num_holes)]

    for hole in range(new_family.num_holes):
        var = model_variable_names[hole]
        if var in partial_model:
            new_family.hole_set_options(hole, [partial_model[var]])

    core, cause_dict = get_counterexample_cores(new_family, quotient, matrix_generator)

    print(cause_dict)
    # # Decide whether we want to compute a counterexample.
    # compute_counterexample = True
    # remove_optimal_holes = True
    # if self.considered_counterexamples == "none":
    #     compute_counterexample = False
    #     remove_optimal_holes = False
    # elif self.considered_counterexamples == "sched":
    #     compute_counterexample = False
    # elif self.considered_counterexamples == "mc" and model == "MDP":
    #     compute_counterexample = False

    # # Check the sub-MDP (see counterexample.py).
    # check_result = check(
    #     self.get_matrix_generator(invert),
    #     new_family,
    #     prop,
    #     compute_counterexample,
    #     remove_optimal_holes,
    #     opponent_holes=opponent_holes,
    # )
    # self.mc_calls += 1
    # all_violated = check_result.all_schedulers_violate
    # # print("All violated", all_violated, check_result.result.at(0))
    # counterexample = check_result.fixed_holes



@click.command()
@click.argument("project_path")
def main(project_path):

    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(
        sketch_path, properties_path
    )
    quotient.build(quotient.family)
    matrix_generator = get_matrix_generator(quotient)

    # seed = random.randint(1, 2**32 - 1)

    # z3.set_param('auto_config', False)

    # z3.set_param('sat.random_seed', seed)
    # z3.set_param('sat.phase', 'random')
    # z3.set_param('sat.random_freq', 0.2)      # default is 0.01
    # z3.set_param('sat.branching.heuristic', 'chb')  # try vsids vs chb
    # z3.set_param('sat.restart', 'luby')       # try luby / geometric / ema

    # # only if you're actually using the lazy SMT stack too
    # z3.set_param('smt.random_seed', seed)

    # z3.set_param("smt.random_seed", random.randint(1, 2**32 - 1))

    constraint = ExistsConstraint()
    constraint.args = argparse.Namespace(deterministic=False)
    queue = Queue()
    process = Process(
        target=molehill.run,
        args=(project_path, "none", constraint),
        kwargs={"mode": "conflicts", "conflict_queue": queue},
    )
    process.start()

    while process.is_alive() or not queue.empty():
        try:
            partial_model = queue.get(timeout=0.1)
        except Empty:
            continue
        process_conflict(partial_model, quotient, matrix_generator)
    process.join()

if __name__ == "__main__":
    main()
