from molehill import run
import argparse
from molehill.constraints import MTBDD, DecisionTree, ExistsConstraint, ExistsForallConstraint

def load_constraint_class(path):
    """
    Load the constraint class from the given path.
    """
    raise RuntimeError("Not implemented yet.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Run the Markov Chain search on a given project path."
    )
    parser.add_argument(
        "project_path", type=str, help="The path to the project directory."
    )
    parser.add_argument(
        "--image", action="store_true", help="Generate an image of the curve."
    )
    # number of tree nodes
    parser.add_argument(
        "--ce",
        type=str,
        default="all",
        help="types of counterexamples to consider",
        choices=["all", "mc", "none"],
    )
    parser.add_argument("--constraint", type=str, choices=["none", "tree", "mtbdd", "existsforall", "custom"], default="none", help="Constraint to use. Built-in constraints are: tree, mtbdd. By setting this to custom, you can implement a custom constraint in project_path/constraint.py. See the README for more information.")
    parser.add_argument("--fsc-memory-size", type=int, default=1, help="Memory size for the considered FSCs")
    parser.add_argument("--reasons", action="store_true", help="Print reasons")
    args, unknown = parser.parse_known_args()

    if args.constraint == "none":
        new_constraint = ExistsConstraint()
    # get class of new constraint
    elif args.constraint == "tree":
        new_constraint = DecisionTree()
    elif args.constraint == "mtbdd":
        new_constraint = MTBDD()
    elif args.constraint == "existsforall":
        new_constraint = ExistsForallConstraint()
    else:
        new_constraint = load_constraint_class(f"{args.project_path}/constraint.py")
    new_parser = argparse.ArgumentParser()
    new_constraint.register_arguments(new_parser)
    new_args = new_parser.parse_args(unknown)
    new_constraint.set_args(new_args)

    run(
        args.project_path,
        args.image,
        args.ce,
        new_constraint,
        fsc_memory_size=args.fsc_memory_size,
        print_reasons=args.reasons,
    )
