import csv
from collections import defaultdict

def analyze_benchexec_csv(file_path):
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
        

    # for row in data_rows:
    #     benchmark = row[0]
    #     cpu_times = []
    #     for tool, col in zip(tool_names, data_columns):
    #         if col < len(row) and row[col].strip().lower() == row[2]:
    #             cpu_time = row[col + 1].strip()
    #             cpu_times.append(cpu_time)
    #         else:
    #             cpu_times.append("NR")
    #     # bold the smallest CPU time
    #     argmin_cpu_time = min(cpu_times, key=lambda x: float(x) if x != "NR" else float('inf'))
    #     cpu_times = [f"\\textbf{{{x}}}" if x == argmin_cpu_time else x for x in cpu_times]
    # Sort data_rows alphabetically by benchmark name

    prefixes = [
        "benchmark-q2-cost",
        "benchmark-q2-tree"
    ]

    for row in data_rows:
        benchmark = row[0].replace(".yml", "")
        for prefix in prefixes:
            if benchmark.startswith(prefix):
                benchmark = benchmark[len(prefix)+1:]
                row[0] = benchmark
                break

    sorted_data_rows = sorted(
        data_rows,
        key=lambda row: row[0]
    )


    # Print LaTeX booktabs table
    print("\\begin{tabular}{l" + "c" * len(tool_names) + "}")
    print("\\toprule")
    print("Benchmark & " + " & ".join(tool_names) + " \\\\")
    print("\\midrule")
    for row_idx, row in enumerate(sorted_data_rows):
        benchmark = row[0].replace(".yml", "").replace("_", "\\_")
        cpu_times = []
        for tool, col in zip(tool_names, data_columns):
            if col < len(row) and row[col].strip().lower() == (row[2] if j > 2 else "true"):
                cpu_time = row[col + 1].strip()
                cpu_times.append(cpu_time)
            else:
                cpu_times.append("NR")
        argmin_cpu_time = min(cpu_times, key=lambda x: float(x) if x != "NR" else float('inf'))
        cpu_times = [f"\\textbf{{{float(x):.2f}}}" if x == argmin_cpu_time and x != "NR" else (f"${float(x):.2f}$" if x != "NR" else "NR") for x in cpu_times]
        print(f"{benchmark} & " + " & ".join(cpu_times) + " \\\\")
    print("\\bottomrule")
    print("\\end{tabular}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python analyze_benchexec_csv.py path/to/tablegenerator.table.csv")
        sys.exit(1)

    analyze_benchexec_csv(sys.argv[1])
