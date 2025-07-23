import csv
from collections import defaultdict
from pathlib import Path
import yaml
import subprocess

def analyze_benchexec_csv(file_path, folder_for_size=None):
    with open(file_path, newline='', encoding='utf-8') as f:
        reader = csv.reader(f, delimiter='\t')
        rows = list(reader)

    tool_row = rows[1]
    metric_row = rows[2]
    expected_order = ['status', 'CPU Time (s)', 'Wall Time (s)', 'Memory (MB)', 'Iterations']
    start = 0
    j = None
    for j, metric in enumerate(metric_row):
        if metric_row[j:j+len(expected_order)] == expected_order:
            start = j
            break
    if j is None:
        raise ValueError("Expected metric row format not found.")
    data_rows = rows[3:]

    data_columns = []
    tool_names = []
    for i, metric in enumerate(metric_row):
        if metric.strip() == "status":
            data_columns.append(i)
            tool_names.append(tool_row[i].strip())

    # Sort tool names alphabetically
    tool_names, data_columns = zip(*sorted(zip(tool_names, data_columns)))

    prefixes = [
        "benchmark-q2-cost",
        "benchmark-q2-tree",
        "pomdps",
        "jair",
        "mdp-families",
        "pomdp-families",
        "other"
    ]

    for row in data_rows:
        if folder_for_size:
            log_file = "SMPMC." + row[0] + ".log"
            with open(Path(folder_for_size) / Path(log_file), "r") as f:
                lines = f.readlines()
                # e.g. 
                # Family size 4.08e+42
                # Quotient size 394
                family_size = "NR"
                nr_states = "NR"
                for line in lines:
                    if "Family size" in line:
                        family_size = line.split()[2]
                        family_size = "$" + family_size.replace("e+", "\\cdot 10^{") + "}$"
                    elif "Quotient size" in line:
                        nr_states = line.split()[2]
                        nr_states = "$" + nr_states + "$"
                row.append(family_size)
                row.append(nr_states)
        if row[0].endswith(".yml"):
            benchmark = row[0].replace(".yml", "")
        for prefix in prefixes:
            if benchmark.startswith(prefix):
                benchmark = benchmark[len(prefix)+1:]
                row[0] = benchmark
            if benchmark[-2] == "_":
                benchmark = benchmark[:-2]
                row[0] = benchmark

    sorted_data_rows = sorted(
        data_rows,
        key=lambda row: row[0]
    )

    if folder_for_size:
        # Add family size and nr states to the header
        tool_names += ("\#Assignments", "\#States")
        data_columns += (-1, -1)

    # Print LaTeX booktabs table
    print("\\begin{tabular}{l" + "c" * len(tool_names) + "}")
    print("\\toprule")
    print("Benchmark & " + " & ".join(tool_names) + " \\\\")
    print("\\midrule")
    for row_idx, row in enumerate(sorted_data_rows):
        benchmark = row[0].replace(".yml", "").replace("_", "\\_")
        cpu_times = []
        for tool, col in zip(tool_names, data_columns):
            if folder_for_size and col == -1:
                # Skip family size and nr states columns for CPU time
                continue
            if col < len(row) and row[col].strip().lower() == (row[2] if j > 2 else "true"):
                cpu_time = row[col + 1].strip()
                cpu_times.append(cpu_time)
            else:
                cpu_times.append("NR")
        argmin_cpu_time = min(cpu_times, key=lambda x: float(x) if x != "NR" else float('inf'))
        cpu_times = [f"\\textbf{{{float(x):.2f}}}" if x == argmin_cpu_time and x != "NR" else (f"${float(x):.2f}$" if x != "NR" else "NR") for x in cpu_times]
        if folder_for_size:
            family_size = row[-2]
            nr_states = row[-1]
            cpu_times.append(family_size)
            cpu_times.append(nr_states)
        print(f"{benchmark} & " + " & ".join(cpu_times) + " \\\\")
    print("\\bottomrule")
    print("\\end{tabular}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) not in [2, 3]:
        print("Usage: python analyze_benchexec_csv.py path/to/tablegenerator.table.csv")
        sys.exit(1)

    folder_for_size = None
    if len(sys.argv) == 3:
        folder_for_size = sys.argv[2]
        if not Path(folder_for_size).is_dir():
            print(f"Error: {folder_for_size} is not a valid directory.")
            sys.exit(1)

    analyze_benchexec_csv(sys.argv[1], folder_for_size=folder_for_size)
