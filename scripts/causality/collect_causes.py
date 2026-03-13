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

import os.path

from itertools import chain

from sklearn import tree
import matplotlib.pyplot as plt

def process_conflict(partial_model, quotient, variables, header, values, labels, running_totals):
    # print(partial_model)

    variable_map = {variables[i]: i for i in range(len(variables))}
    labels_map = {labels[i]: i for i in range(len(labels))}

    X = values
    Y = [labels_map["*"] for _row in range(len(values))]
    print(Y)
    print(labels_map)
    for var in partial_model:
        var_index = variable_map[var] # the same as hole_index
        label = quotient.family.hole_to_option_labels[var_index][partial_model[var]]
        Y[var_index] = labels_map[label]
    # print(X, Y)

    clf = tree.DecisionTreeClassifier()
    clf = clf.fit(X, Y)

    tree_size = clf.tree_.node_count

    if tree_size >= running_totals["smallest"]:
        return
    running_totals["smallest"] = tree_size
    n_features = len(header)
    # Adjust plot size dynamically based on tree structure
    n_nodes = clf.tree_.node_count
    max_depth = clf.tree_.max_depth
    width = max(5, n_features * 2)
    height = max(5, (max_depth + 1) * 2, n_nodes // 2)

    print(X, Y, labels)

    class_names = [labels[c] for c in clf.classes_]

    fig, ax = plt.subplots(figsize=(width, height))
    tree.plot_tree(
        clf,
        feature_names=header,
        class_names=class_names,
        filled=True,
        rounded=True,
        fontsize=12,
        ax=ax
    )
    plt.tight_layout()
    plt.savefig(f"pics/tree_{tree_size}.png", bbox_inches="tight")
    plt.close(fig)
@click.command()
@click.argument("project_path")
def main(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(
        sketch_path, properties_path
    )
    family = quotient.family
    quotient.build(family)

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

    vars_to_states = dict()

    choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
    transition_matrix = quotient.quotient_mdp.transition_matrix
    # go through transition matrix 
    hole_indices = set()
    for state in range(quotient.quotient_mdp.nr_states):
        first_row = transition_matrix.get_rows_for_group(state)[0]
        if len(choice_to_hole_options[first_row]) == 0:
            assert len(transition_matrix.get_rows_for_group(state)) == 1, "Input model not an MDP"
            continue
        hole_index = choice_to_hole_options[first_row][0][0]
        assert hole_index not in hole_indices, "Multiple states have the same hole, not supported"
        hole_indices.add(hole_index)
        var_name = family.hole_name(hole_index)
        for row in transition_matrix.get_rows_for_group(state):
            assert choice_to_hole_options[row][0][0] == hole_index, "Multiple holes for one state, not supported"
            assert len(choice_to_hole_options[row]) == 1, "Multiple choices for one state, not supported"
            vars_to_states[var_name] = state

    variables = list(vars_to_states.keys())
    # print(variables)

    labels = list(
        dict.fromkeys(
            chain(
                *[quotient.family.hole_to_option_labels[i] for i in hole_indices]
            )
        )
    ) + ["*"] # special whatever label maps to max(actions)+1

    # print(labels)

    values_orig = []
    header = []
    with open(os.path.join(project_path, "values.csv"), "r", encoding="utf-8") as f:
        header = f.readline().strip().split(",")
        for line in f:
            values = line.strip().split(",")
            values_orig.append(
                [float(values[i]) for i in range(len(header))]
            )

    values = []

    choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
    transition_matrix = quotient.quotient_mdp.transition_matrix

    # go through transition matrix 
    for state in vars_to_states.values():
        values.append(values_orig[state])
    
    constraint = ExistsConstraint()
    constraint.args = argparse.Namespace(deterministic=False)
    queue = Queue()
    process = Process(
        target=molehill.run,
        args=(project_path, "conflicts", constraint),
        kwargs={"mode": "conflicts", "conflict_queue": queue},
    )
    process.start()

    running_totals = {
        "smallest": float("inf"),
    }
    while process.is_alive() or not queue.empty():
        try:
            partial_model = queue.get(timeout=0.1)
        except Empty:
            continue
        process_conflict(partial_model, quotient, variables, header, values, labels, running_totals)
    process.join()

if __name__ == "__main__":
    main()
