from molehill import run
import argparse
from molehill.decision_tree import build_decision_tree, draw_tree

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
    parser.add_argument("--tree", action="store_true", help="Build a tree.")
    parser.add_argument("--diseq", action="store_true", help="Track disequalities as well.")
    # number of tree nodes
    parser.add_argument("--depth", type=int, help="Depth of the tree.", default=4)
    parser.add_argument("--nodes", type=int, help="Number of enabled nodes in the tree.", default=None)
    parser.add_argument(
        "--ce", type=str, default="all", help="types of counterexamples to consider", choices=["all", "mc", "none"]
    )
    parser.add_argument("--deterministic", action="store_true", help="Deterministic Z3 assignment.", default=None)
    args = parser.parse_args()

    constraint_lambda = None
    postprocess_lambda = None
    if args.tree:
        constraint_lambda = lambda variables: build_decision_tree(variables, args.depth, args.nodes)
        postprocess_lambda = lambda model, variables: draw_tree(model, args.depth, variables)

    run(args.project_path, args.image, args.ce, None, constraint_lambda, postprocess_lambda, not args.deterministic, track_disequalities=args.diseq)
