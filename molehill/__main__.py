from molehill import run
import argparse
from molehill.constraints import (
    MTBDD,
    DecisionTree,
    ExistsConstraint,
    ExistsForallConstraint,
    ForallExistsConstraint,
    ProbGoal,
    CostsConstraint
)


def load_constraint_class(path):
    """
    Load the constraint class from the given path.
    """
    with open(path, "r", encoding="utf-8") as f:
        code = f.read()
    # arbitary code execution >:)
    exec(code, globals())
    if "CustomConstraint" not in globals():
        raise ValueError("No class named CustomConstraint found in constraint.py")
    return globals()["CustomConstraint"]()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Run the Markov Chain search on a given project path."
    )
    parser.add_argument(
        "project_path", type=str, help="The path to the project directory."
    )
    parser.add_argument("--exact", action="store_true", help="Exact mode.")
    parser.add_argument(
        "--image", action="store_true", help="Generate an image of the curve."
    )
    parser.add_argument(
        "--plot-args", action="store_true", help="Plot function arguments."
    )
    parser.add_argument("--verbose", action="store_true", help="Verbose mode.")
    # number of tree nodes
    parser.add_argument(
        "--ce",
        type=str,
        default="none",
        help="Types of counterexamples to consider. None: no counterexamples, Sched: Additionally analyze schedulers, MC: Additionally analyze Markov chains, All: Analyze all counterexamples",
        choices=["all", "mc", "sched", "none"],
    )
    parser.add_argument(
        "--constraint",
        type=str,
        choices=[
            "none",
            "tree",
            "mtbdd",
            "existsforall",
            "forallexists",
            "existsforalltree",
            "prob0",
            "prob1",
            "costs",
            "custom",
        ],
        default="none",
        help="Constraint to use. Built-in constraints are: tree, mtbdd. By setting this to custom, you can implement a custom constraint in project_path/constraint.py. See the README for more information.",
    )
    parser.add_argument(
        "--fsc-memory-size",
        type=int,
        default=1,
        help="Memory size for the considered FSCs",
    )
    parser.add_argument("--reasons", action="store_true", help="Print reasons")
    parser.add_argument("--pure-smt", action="store_true", help="Use pure SMT solver")
    parser.add_argument("--print-size", action="store_true", help="Print size of the problem and quit")

    parser.add_argument("--dump-cache", type=str, default=None, help="Dump the cache to a file")
    parser.add_argument("--load-cache", type=str, default=None, help="Load the cache from a file")
    args, unknown = parser.parse_known_args()

    if args.constraint == "none":
        new_constraint = ExistsConstraint()
    # get class of new constraint
    elif args.constraint == "tree":
        new_constraint = DecisionTree()
    elif args.constraint == "existsforalltree":
        new_constraint = DecisionTree(robust=True)
    elif args.constraint == "mtbdd":
        new_constraint = MTBDD()
    elif args.constraint == "existsforall":
        new_constraint = ExistsForallConstraint()
    elif args.constraint == "forallexists":
        new_constraint = ForallExistsConstraint()
    elif args.constraint == "prob0":
        new_constraint = ProbGoal(prob=0)
    elif args.constraint == "prob1":
        new_constraint = ProbGoal(prob=1)
    elif args.constraint == "costs":
        new_constraint = CostsConstraint(project_path=args.project_path)
    else:
        new_constraint = load_constraint_class(f"{args.project_path}/constraint.py")
    new_parser = argparse.ArgumentParser()
    print(f"Using constraint: {new_constraint.__class__.__name__}")
    new_constraint.register_arguments(new_parser)
    new_args = new_parser.parse_args(unknown)
    new_constraint.set_args(new_args)

    run(
        args.project_path,
        args.ce,
        new_constraint,
        exact=args.exact,
        fsc_memory_size=args.fsc_memory_size,
        print_reasons=args.reasons,
        image=args.image,
        plot_function_args=args.plot_args,
        verbose=args.verbose,
        pure_smt=args.pure_smt,
        dump_cache=args.dump_cache,
        load_cache=args.load_cache,
        print_size=args.print_size
    )
