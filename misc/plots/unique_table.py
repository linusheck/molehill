import csv
from collections import defaultdict

def analyze_benchexec_csv(file_path):
    with open(file_path, newline='', encoding='utf-8') as f:
        reader = csv.reader(f, delimiter='\t')
        rows = list(reader)

    tool_row = rows[1]
    metric_row = rows[2]
    data_rows = rows[3:]

    expected_order = ['status', 'CPU Time (s)', 'Wall Time (s)', 'Memory (MB)', 'Iterations']
    j = None
    for j, metric in enumerate(metric_row):
        if metric_row[j:j+len(expected_order)] == expected_order:
            start = j
            break
    if j is None:
        raise ValueError("Expected metric row format not found.")


    status_columns = []
    tool_names = []
    for i, metric in enumerate(metric_row):
        if metric.strip().lower() == "status":
            status_columns.append(i)
            tool_names.append(tool_row[i].strip())

    solved_count = defaultdict(int)
    unique_solved_count = defaultdict(int)

    for row in data_rows:
        solved_tools = []
        for tool, col in zip(tool_names, status_columns):
            if col < len(row) and row[col].strip().lower() == (row[2] if j > 2 else "true"):
                if tool == "PAYNT-AR-MDP-Eval":
                    continue # This tool is in the appendix
                solved_count[tool] += 1
                solved_tools.append(tool)
        if len(solved_tools) == 1:
            unique_solved_count[solved_tools[0]] += 1

    print(f"Total number of problems: {len(data_rows)}")
    print(f"{'Tool':<25} {'Solved':>7} {'Uniquely Solved':>18}")
    print("-" * 50)
    for tool in sorted(tool_names):
        print(f"{tool:<25} {solved_count[tool]:>7} {unique_solved_count[tool]:>18}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python analyze_benchexec_csv.py path/to/tablegenerator.table.csv")
        sys.exit(1)

    analyze_benchexec_csv(sys.argv[1])
