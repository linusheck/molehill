import subprocess
import sys
from pathlib import Path

def main():
    if len(sys.argv) != 3:
        print("Usage: python constrained_benchmark.py <paynt|molehill> <folder>")
        sys.exit(1)

    method = sys.argv[1]
    folder = sys.argv[2]

    if method not in ["paynt", "molehill", "smtlra"]:
        print("Method must be either 'paynt', 'molehill' or 'smtlra'")
        sys.exit(1)
    

    args_file = Path(folder) / "args.txt"
    if not args_file.exists():
        print(f"Setup file {args_file} does not exist.")
        sys.exit(1)
    cli_args = args_file.read_text().strip()

    invocation = None
    if method == "paynt":
        invocation = [
            "python",
            "build/paynt/paynt.py",
            folder,
            "--method",
            "cegis",
        ]
    elif method == "molehill":
        invocation = [
            "python",
            "-m",
            "molehill",
            folder,
        ]
    elif method == "smtlra":
        invocation = [
            "python",
            "-m",
            "molehill",
            "--pure-smt",
            folder,
        ]

    invocation.extend(cli_args.split())

    process = subprocess.Popen(
        invocation,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    for line in process.stdout:
        print(line, end="")  # Already includes newline

    process.wait()


if __name__ == "__main__":
    main()
