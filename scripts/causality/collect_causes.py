import time as _time
import shutil
import tempfile

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
from collections import Counter
import json

def process_conflict(partial_model, quotient, variables, header, values, labels, running_totals):
    # print(partial_model)

    variable_map = {variables[i]: i for i in range(len(variables))}
    labels_map = {labels[i]: i for i in range(len(labels))}

    X = values
    Y = [labels_map["*"] for _row in range(len(values))]
    for var in partial_model:
        var_index = variable_map[var] # the same as hole_index
        label = quotient.family.hole_to_option_labels[var_index][partial_model[var]]
        Y[var_index] = labels_map[label]
    # print(X, Y)

    clf = tree.DecisionTreeClassifier()
    clf = clf.fit(X, Y)

    tree_size = clf.tree_.node_count
    cause_size = len(partial_model)

    running_totals["tree_size_counts"][tree_size] += 1
    running_totals["cause_size_counts"][cause_size] += 1
    if cause_size < running_totals["smallest_cause"]:
        running_totals["smallest_cause"] = cause_size

    if tree_size >= running_totals["smallest"]:
        return
    running_totals["smallest"] = tree_size
    n_features = len(header)
    # Adjust plot size dynamically based on tree structure
    n_nodes = clf.tree_.node_count
    max_depth = clf.tree_.max_depth
    width = 2*max(10, n_features * 1.75, max_depth * 2.25)
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
@click.option("--threshold", type=float, default=None, help="Override the threshold in sketch.props")
@click.option("--time-limit", type=int, default=None, help="Stop collecting after this many seconds")
def main(project_path, threshold, time_limit):
    # If --threshold is given, create a temporary project dir with an overridden sketch.props
    actual_project_path = project_path
    tmp_dir = None
    if threshold is not None:
        original_props = open(f"{project_path}/sketch.props").read().strip()
        import re
        # Replace the numeric threshold in the property string
        new_props = re.sub(
            r'(P\s*[<>=]+\s*)([0-9.eE+\-]+)',
            lambda m: m.group(1) + str(threshold),
            original_props
        )
        tmp_dir = tempfile.mkdtemp(prefix="causality_bench_")
        shutil.copy(f"{project_path}/sketch.templ", f"{tmp_dir}/sketch.templ")
        with open(f"{tmp_dir}/sketch.props", "w") as f:
            f.write(new_props + "\n")
        actual_project_path = tmp_dir
    sketch_path = f"{actual_project_path}/sketch.templ"
    properties_path = f"{actual_project_path}/sketch.props"
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
        args=(actual_project_path, "conflicts", constraint),
        kwargs={"mode": "conflicts", "conflict_queue": queue},
    )
    process.start()

    running_totals = {
        "smallest": float("inf"),
        "conflicts_processed": 0,
        "tree_size_counts": Counter(),
        "cause_size_counts": Counter(),
        "smallest_cause": float("inf"),
    }
    start_time = _time.monotonic()
    deadline = start_time + time_limit if time_limit is not None else None
    timed_out = False
    while process.is_alive() or not queue.empty():
        if deadline is not None and _time.monotonic() >= deadline:
            timed_out = True
            break
        try:
            partial_model = queue.get(timeout=0.1)
        except Empty:
            continue
        running_totals["conflicts_processed"] += 1
        process_conflict(partial_model, quotient, variables, header, values, labels, running_totals)

    if timed_out:
        process.terminate()

    elapsed = _time.monotonic() - start_time
    smallest = running_totals["smallest"]
    smallest_str = str(int(smallest)) if smallest != float("inf") else "none"
    smallest_cause = running_totals["smallest_cause"]
    smallest_cause_str = str(int(smallest_cause)) if smallest_cause != float("inf") else "none"
    effective_threshold = threshold if threshold is not None else "original"

    tree_counts = running_totals["tree_size_counts"]
    cause_counts = running_totals["cause_size_counts"]

    print(f"CAUSALITY_RESULT"
          f" threshold={effective_threshold}"
          f" smallest_tree_nodes={smallest_str}"
          f" smallest_cause={smallest_cause_str}"
          f" causes={running_totals['conflicts_processed']}"
          f" elapsed_seconds={elapsed:.2f}"
          f" timed_out={'yes' if timed_out else 'no'}",
          flush=True)

    # --- Everything below is best-effort; benchexec may kill us here ---

    if timed_out:
        process.join(timeout=5)
        if process.is_alive():
            process.kill()
            process.join()
        # drain remaining queue items
        while not queue.empty():
            try:
                partial_model = queue.get_nowait()
                running_totals["conflicts_processed"] += 1
                process_conflict(partial_model, quotient, variables, header, values, labels, running_totals)
            except Empty:
                break
    else:
        process.join()

    # --- Distribution tables ---
    if tree_counts:
        print("\n=== Tree size distribution ===")
        for sz in sorted(tree_counts):
            print(f"  nodes={sz}  count={tree_counts[sz]}")
    else:
        print("\nNo trees found.")

    if cause_counts:
        print("\n=== Cause size distribution ===")
        for sz in sorted(cause_counts):
            print(f"  variables={sz}  count={cause_counts[sz]}")

    # --- Distribution histograms ---
    os.makedirs("pics", exist_ok=True)

    if tree_counts:
        sizes = sorted(tree_counts)
        counts = [tree_counts[s] for s in sizes]
        fig, ax = plt.subplots(figsize=(max(6, (max(sizes) - min(sizes) + 2) * 0.6), 4))
        ax.bar(sizes, counts, color="steelblue", width=0.8)
        ax.set_xlabel("Tree size (nodes)")
        ax.set_ylabel("Count")
        ax.set_title("Decision tree size distribution")
        ax.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
        ax.yaxis.set_major_locator(plt.MaxNLocator(integer=True))
        for s, v in zip(sizes, counts):
            ax.text(s, v + 0.3, str(v), ha="center", fontsize=9)
        plt.tight_layout()
        plt.savefig("pics/tree_size_distribution.png", bbox_inches="tight")
        plt.close(fig)

    if cause_counts:
        sizes = sorted(cause_counts)
        counts = [cause_counts[s] for s in sizes]
        fig, ax = plt.subplots(figsize=(max(6, (max(sizes) - min(sizes) + 2) * 0.6), 4))
        ax.bar(sizes, counts, color="darkorange", width=0.8)
        ax.set_xlabel("Cause size (variables)")
        ax.set_ylabel("Count")
        ax.set_title("Cause size distribution")
        ax.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
        ax.yaxis.set_major_locator(plt.MaxNLocator(integer=True))
        for s, v in zip(sizes, counts):
            ax.text(s, v + 0.3, str(v), ha="center", fontsize=9)
        plt.tight_layout()
        plt.savefig("pics/cause_size_distribution.png", bbox_inches="tight")
        plt.close(fig)

    if tmp_dir is not None:
        shutil.rmtree(tmp_dir, ignore_errors=True)
if __name__ == "__main__":
    main()