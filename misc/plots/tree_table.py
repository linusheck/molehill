#!/usr/bin/env python3
"""
CSV-to-LaTeX converter (no pandas)

Usage:
    python csv_to_latex_no_pandas.py tablegenerator.table.csv > tables.tex
The input must be the tab-separated file produced by your benchmark runner.
The script prints one LaTeX table per method (e.g. SMPMC, SMT(LRA)).
"""
import csv, re, sys
from collections import defaultdict

def extract_info(filename: str):
    """Return (base_name, node) from benchmark filename or (None, None)."""
    # Examples:
    # benchmark-general-sat_mem_1_avoid-8-2-big-family_9.yml
    # benchmark-q2-tree-sat_refuel-06_7.yml
    position_of_sat = filename.find("sat_")
    name = filename[position_of_sat + 4:]
    name = name.replace(".yml", "")
    nodes = int(name.split("_")[-1])
    name = "_".join(name.split("_")[:-1])
    return (name, nodes)


def status_to_str(status):
    if status == "true": return "\\yes{}"
    elif status == "false": return "\\no{}"
    assert False

def format_cell(status, cpu):
    if not status:                  return "NR"
    if status == "TIMEOUT":         return "NR"
    if status == "OUT OF MEMORY":   return "NR"
    return f"{status_to_str(status)} {float(cpu):.2f}" if cpu else status_to_str(status)

def read_table(path):
    rows = list(csv.reader(open(path, newline='', encoding='utf-8'), delimiter='\t'))
    if len(rows) < 4:
        sys.exit("Input file too short or wrong format")

    method_cols = {}                      # method → first column index
    for idx, hdr in enumerate(rows[1]):   # second row holds method names
        if hdr and "Benchmarks" in hdr and hdr not in method_cols:
            method_cols[hdr] = idx

    data      = {m: defaultdict(tuple) for m in method_cols}
    bases     = defaultdict(set)
    nodes_set = defaultdict(set)

    for r in rows[3:]:
        if not r or not r[0]:
            continue
        base, node = extract_info(r[0])
        if base is None:
            continue
        for m, c in method_cols.items():
            status = r[c]     if c     < len(r) else ""
            cpu    = r[c + 1] if c + 1 < len(r) else ""
            data[m][(base, node)] = (status, cpu)
            bases[m].add(base)
            nodes_set[m].add(node)
    return data, bases, nodes_set

# ---------- LaTeX generation -------------------------------------------------
def latex_table(method, dat, base_names, node_numbers):
    nodes = sorted(node_numbers)
    lines = [
        r"\begin{table*}",
        "\small"
        r"\centering",
        r"\begin{tabular}{" + "l" + "c"*len(nodes) + "}",
        r"\toprule",
        "Benchmark & " + " & ".join(str(n) for n in nodes) + r" \\",
        r"\midrule"
    ]
    for b in sorted(base_names):
        disp = b.replace("sat_", "").replace(".yml", "")
        if "mem_1_" in disp:
            disp = disp.replace("mem_1_", "")
        disp = disp.replace("big-family", "bf")
        disp = disp.replace("_", "\\_")
        cells = [format_cell(*dat.get((b, n), ("", ""))) for n in nodes]
        lines.append(disp + " & " + " & ".join(cells) + r" \\")
    method = method.replace(".Benchmarks", "")
    lines += [r"\bottomrule", r"\end{tabular}", rf"\caption{{{method} Results for \Ca}}",  r"\end{table*}", ""]
    return "\n".join(lines)

# ---------- main -------------------------------------------------------------
def main(fname):
    data, bases, nodes = read_table(fname)
    for m in data:
        print(f"% Table for {m}")
        print(latex_table(m, data[m], bases[m], nodes[m]))

if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: python csv_to_latex_no_pandas.py <tsv_file>")
    main(sys.argv[1])
