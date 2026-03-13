#!/usr/bin/env python3
"""
Generate BenchExec setup for causality threshold grid-search experiments.

For each of the three causality models (5days, icu, lunar), this script:
  1. Parses the sketch.props to find the target label (e.g. [F "good"])
  2. Computes Pmin and Pmax over the MDP to get the reachability range
  3. Generates 10 YAML benchmark tasks with thresholds evenly spaced in [min, max]
  4. Writes a comparison_causality.xml BenchExec definition

Usage (from repo root):
    python scripts/causality/create_benchexec_setup.py

Then run:
    scripts/benchmark.sh causality <threads>
"""

import os
import re
import sys

import stormpy

MODELS = ["5days", "icu", "lunar"]
NUM_THRESHOLDS = 10
TIME_LIMIT = 3600  # 1 hour per run

RESOURCES_ROOT = "resources/causality"
BENCHMARKS_DIR = "benchmarks/files/causality-grid"
COMPARISON_XML = "comparison_causality.xml"
PROPERTY_FILE = "benchmarks/unknown.txt"


def parse_target_label(props_path):
    """Extract the target label from sketch.props, e.g. 'good' from 'P>=0.5 [F "good"]'."""
    content = open(props_path).read().strip()
    m = re.search(r'\[\s*F\s+"([^"]+)"\s*\]', content)
    if not m:
        raise ValueError(f"Cannot parse target label from {props_path}: {content!r}")
    return m.group(1)


def parse_operator_and_formula(props_path):
    """Return (full original property string, operator+threshold prefix, eventual part)."""
    content = open(props_path).read().strip()
    # e.g. "P>=0.5 [F \"good\"]" -> prefix="P>=0.5", formula="[F \"good\"]"
    m = re.match(r'(P\s*[<>=]+\s*[0-9.eE+\-]+)\s*(\[.+\])', content)
    if not m:
        raise ValueError(f"Cannot parse property from {props_path}: {content!r}")
    return content, m.group(1), m.group(2)


def compute_range(model_dir, target_label):
    """Compute Pmin and Pmax over the MDP for the given target label."""
    drn_path = os.path.join(model_dir, "mdp.drn")
    model = stormpy.build_model_from_drn(drn_path)
    prop_min = stormpy.parse_properties_without_context(f'Pmin=? [F "{target_label}"]')[0]
    prop_max = stormpy.parse_properties_without_context(f'Pmax=? [F "{target_label}"]')[0]
    res_min = stormpy.check_model_sparse(model, prop_min)
    res_max = stormpy.check_model_sparse(model, prop_max)
    init = model.initial_states[0]
    return float(res_min.at(init)), float(res_max.at(init))


def linspace(lo, hi, n):
    """Return n evenly spaced values from lo to hi inclusive."""
    if n == 1:
        return [lo]
    step = (hi - lo) / (n - 1)
    return [lo + i * step for i in range(n)]


def write_yml(path, input_dir, threshold):
    """Write a single BenchExec YAML task file."""
    # input_dir is relative from benchmarks/files/causality-grid/ to the resource dir
    content = f"""
format_version: "2.0"

input_files:
- {input_dir}

properties:
  - property_file: ../../unknown.txt

options:
    threshold: {threshold}
    time_limit: {TIME_LIMIT}
"""
    with open(path, "w") as f:
        f.write(content)


def write_comparison_xml(path, tasks_glob):
    """Write the BenchExec comparison XML."""
    content = f"""<?xml version="1.0" encoding="UTF-8"?>
<benchmark tool="tools.causality_collect" timelimit="{TIME_LIMIT}s" hardtimelimit="{TIME_LIMIT}s" memlimit="16GB">
  <tasks name="Causality Benchmarks">
    <include>{tasks_glob}</include>
    <propertyfile>{PROPERTY_FILE}</propertyfile>
  </tasks>

  <rundefinition name="Collect-Causes">
    <column title="Threshold" value="threshold"/>
    <column title="Smallest Tree" value="smallest_tree_nodes"/>
    <column title="Conflicts" value="conflicts_processed"/>
    <column title="Elapsed (s)" value="elapsed_seconds"/>
    <column title="Timed Out" value="timed_out"/>
    <column title="Tree Size Dist" value="tree_size_dist"/>
    <column title="Cause Size Dist" value="cause_size_dist"/>
    <require cpuCores="1"/>
    <option>scripts/causality/collect_causes.py</option>
  </rundefinition>
</benchmark>
"""
    with open(path, "w") as f:
        f.write(content)


def main():
    os.makedirs(BENCHMARKS_DIR, exist_ok=True)

    # Clean old generated files
    for f in os.listdir(BENCHMARKS_DIR):
        if f.startswith("causality-") and f.endswith(".yml"):
            os.remove(os.path.join(BENCHMARKS_DIR, f))

    total = 0
    for model_name in MODELS:
        model_dir = os.path.join(RESOURCES_ROOT, model_name)
        props_path = os.path.join(model_dir, "sketch.props")

        target_label = parse_target_label(props_path)
        p_min, p_max = compute_range(model_dir, target_label)

        thresholds = linspace(p_min, p_max, NUM_THRESHOLDS)

        print(f"{model_name}: label={target_label!r}  range=[{p_min}, {p_max}]")
        for i, thresh in enumerate(thresholds):
            name = f"causality-{model_name}-{i:02d}"
            yml_path = os.path.join(BENCHMARKS_DIR, f"{name}.yml")
            # Relative path from benchmarks/files/causality-grid/ -> resources/causality/<model>
            input_dir = f"../../../{RESOURCES_ROOT}/{model_name}"
            write_yml(yml_path, input_dir, thresh)
            print(f"  {name}.yml  threshold={thresh}")
            total += 1

    tasks_glob = f"{BENCHMARKS_DIR}/*.yml"
    write_comparison_xml(COMPARISON_XML, tasks_glob)

    print(f"\nGenerated {total} benchmark tasks in {BENCHMARKS_DIR}/")
    print(f"Generated {COMPARISON_XML}")
    print(f"\nTo run:  scripts/benchmark.sh causality <threads>")


if __name__ == "__main__":
    main()
