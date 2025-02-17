"""Molehill is a Markov chain searcher."""

import paynt.quotient
import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import math

from molehill.plugin import SearchMarkovChain

def run(project_path, image, considered_counterexamples, custom_solver_settings=None, custom_constraint_lambda=None, postprocess_lambda=None, random_assignment=False, search_space_test=False):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)

    # print all python properties of quotient
    family = quotient.family

    # quotient.build(family)

    print("Done")
    s = z3.Solver()

    if random_assignment:
        s.set("phase_selection", 5)

    if custom_solver_settings:
        custom_solver_settings(s)

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

    # add variables that are constants so we can listen to diseq
    # map from #bits to list of constants
    constants = []
    constant_expr = []
    ranges = []
    var_ranges = []
    bit_nums = set()
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        bit_nums.add(num_bits)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        # it gets guaranteed by paynt that this is actually the range
        # (these are just the indices, not the actual values in the final model :)
        ranges.append(
            z3.And(
                var >= z3.BitVecVal(min(options), num_bits),
                var <= z3.BitVecVal(max(options), num_bits),
            )
        )
        var_ranges.append(max(options))
        for i in range(0, 2**num_bits):
            c = z3.Bool(f"{var}!={i}")
            constants.append(c)
            constant_expr.append(c == (var != z3.BitVecVal(i, num_bits)))
    
    s.add(ranges)
    s.add(constant_expr)

    if custom_constraint_lambda:
        s.add(custom_constraint_lambda(variables))

    # add test z3 constraints
    # s.add(variables[0] + variables[1] == variables[2])
    # s.add(variables[0] == 0)
    # s.add(variables[1] == 0)

    p = SearchMarkovChain(s, quotient, var_ranges, draw_image=(image or search_space_test), considered_counterexamples=considered_counterexamples)
    p.register_variables(variables, constants)
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
        if postprocess_lambda:
            postprocess_lambda(model, variables)
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
