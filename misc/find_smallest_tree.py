import subprocess
import sys


def main():
    if len(sys.argv) != 2:
        print("Usage: python run_until_sat.py <arg1>")
        sys.exit(1)

    arg1 = sys.argv[1]
    x = 1

    while True:
        print(f"Running with --nodes {x}")
        process = subprocess.Popen(
            [
                "python",
                "-m",
                "molehill",
                arg1,
                "--constraint",
                "existsforalltree",
                "--nodes",
                str(x),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )

        found_sat = False
        for line in process.stdout:
            print(line, end="")  # Already includes newline
            if line.strip() == "sat":
                found_sat = True

        process.wait()

        if found_sat:
            break

        x += 2


if __name__ == "__main__":
    main()
