import sys
import os
import csv

def process_file(input_path):
    with open(input_path, newline='') as f:
        reader = csv.reader(f, delimiter="\t")
        rows = list(reader)

    if not rows:
        print("Empty file.")
        return

    # Modify the data rows
    for row in rows[3:]:
        assert len(row) == 11
        for status_idx, cputime_idx, walltime_idx, _memory in [(3, 4, 5, 6), (7, 8, 9, 10)]:
            status = row[status_idx].strip().lower()
            if status != row[2]:
                row[cputime_idx] = "30000"
                row[walltime_idx] = "30000"
    output_path = input_path

    with open(output_path, "w", newline='') as f:
        writer = csv.writer(f, delimiter="\t")
        writer.writerows(rows)

if __name__ == "__main__":
    process_file(sys.argv[1])
