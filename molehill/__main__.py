import paynt.quotient
import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import json
import math


# from molehill.curve_drawer import draw_curve
from molehill.decision_tree import build_decision_tree, draw_tree
from molehill.plugin import SearchMarkovChain
import argparse


def run(project_path, image, custom_constraint_lambda=None):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)

    # print all python properties of quotient
    family = quotient.family

    quotient.build(family)

    print("Done")
    s = z3.Solver()

    # set random phase selection
    s.set("phase_selection", 5)

    variables = []
    # create variables
    num_bits = (
        max(
            [
                math.ceil(math.log2(max(family.hole_options(hole)) + 1))
                for hole in range(family.num_holes)
            ]
        )
        + 1
    )
    
    ranges = []
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        # TODO hole options of full family should be a sorted vector of indices that is continous
        ranges.append(
            z3.And(
                var >= z3.BitVecVal(min(options), num_bits),
                var <= z3.BitVecVal(max(options), num_bits),
            )
        )

    s.add(ranges)

    if custom_constraint_lambda:
        s.add(custom_constraint_lambda(variables))


    if tree:
        s.add()

    # add test z3 constraints
    # s.add(variables[0] + variables[1] == variables[2])
    # s.add(variables[0] == 0)
    # s.add(variables[1] == 0)

    p = SearchMarkovChain(s, quotient, draw_image=image)
    p.register_variables(variables)
    model = None
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # re-check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
        if tree:
            draw_tree(model, depth, variables)
    else:
        print("unsat")
    print(f"Considered {p.considered_models} models")
    if sum(p.mdp_fails_and_wins) > 0:
        print(
            f"MDP checking had {p.mdp_fails_and_wins[0]} fails and {p.mdp_fails_and_wins[1]} wins ({round(p.mdp_fails_and_wins[1] / sum(p.mdp_fails_and_wins) * 100, 1)}% wins)"
        )

    if image:
        print("Drawing image")
        from molehill.curve_drawer import draw_curve

        draw_curve(num_bits, variables, s, p, model)

    # return is for testing purposes
    return model, s, p


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
    # number of tree nodes
    parser.add_argument("--depth", type=int, help="Depth of the tree.", default=4)
    parser.add_argument("--nodes", type=int, help="Number of enabled nodes in the tree.", default=None)
    args = parser.parse_args()

    constraint_lambda = None
    if args.tree:
        constraint_lambda = lambda variables: build_decision_tree(variables, args.depth, args.nodes)

    run(args.project_path, args.image, constraint_lambda)
