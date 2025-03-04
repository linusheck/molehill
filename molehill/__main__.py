from molehill import run
import argparse
from molehill.constraints.mtbdd import MTBDD
from molehill.constraints.tree import DecisionTree

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
    parser.add_argument(
        "--deterministic",
        action="store_true",
        help="Deterministic Z3 assignment.",
        default=None,
    )
    parser.add_argument("--constraint", type=str, choices=["none", "tree", "mtbdd", "custom"], default="none", help="Constraint to use. Built-in constraints are: tree, mtbdd. By setting this to custom, you can implement a custom constraint in project_path/constraint.py. See the README for more information.")
    parser.add_argument("--fsc-memory-size", type=int, default=1, help="Memory size for the considered FSCs")
    args, unknown = parser.parse_known_args()


    constraint_lambda = None
    postprocess_lambda = None
    if args.constraint != "none":
        # get class of new constraint
        if args.constraint == "tree":
            new_constraint = DecisionTree()
        elif args.constraint == "mtbdd":
            new_constraint = MTBDD()
        else:
            new_constraint = load_constraint_class(f"{args.project_path}/constraint.py")
        new_parser = argparse.ArgumentParser()
        new_constraint.register_arguments(new_parser)
        new_args = new_parser.parse_args(unknown)
        constraint_lambda = lambda variables: new_constraint.build_constraint(variables, new_args)
        postprocess_lambda = lambda model, variables: new_constraint.show_result(model, variables)
    else:
        assert unknown == [], "Superflous arguments: " + str(unknown)

    run(
        args.project_path,
        args.image,
        args.ce,
        None,
        constraint_lambda,
        postprocess_lambda,
        not args.deterministic,
        fsc_memory_size=args.fsc_memory_size
    )
