def compute_avg_ratios(file_path):
    with open(file_path, "r", encoding="utf-8") as f:
        lines = [line.strip() for line in f if line.strip()]

    header = [col.strip() for col in lines[2].split("\t")]

    # Get relevant column indices
    status1_idx = header.index("status")
    cpu1_idx = header.index("CPU Time (s)")
    status2_idx = header.index("status", status1_idx + 1)
    cpu2_idx = header.index("CPU Time (s)", cpu1_idx + 1)

    times_a = []
    times_b = []

    for line in lines[3:]:
        cols = [col.strip() for col in line.split("\t")]
        if len(cols) <= max(cpu2_idx, status2_idx):
            continue

        status1 = cols[status1_idx].lower()
        status2 = cols[status2_idx].lower()

        print(status1, status2)

        if not (status1 in ["true", "false"] and status2 in ["true", "false"]):
            continue
        try:
            cpu1 = float(cols[cpu1_idx])  # A: synthesis
            cpu2 = float(cols[cpu2_idx])  # B: SMT
        except ValueError:
            continue

        if cpu1 <= 0 or cpu2 <= 0:
            assert False

        times_a.append(cpu1)
        times_b.append(cpu2)

    if times_a:
        avg_a = sum(times_a) / len(times_a)
        avg_b = sum(times_b) / len(times_b)
        ratio = avg_b / avg_a
        print(f"Average CPU Time A: {avg_a:.2f} s, Average CPU Time B: {avg_b:.2f} s, Ratio: {ratio:.2f}")
    else:
        print("No comparable cases found.")

import sys
compute_avg_ratios(sys.argv[1])