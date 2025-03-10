"""Molehill is a Markov chain searcher."""

import paynt.quotient
import paynt.quotient.pomdp
import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import math
import payntbind.synthesis

from molehill.mole import Mole


def run(
    project_path,
    image,
    considered_counterexamples,
    constraint,
    search_space_test=False,
    fsc_memory_size=1,
    exact=False,
    print_reasons=False,
):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    paynt.quotient.pomdp.PomdpQuotient.initial_memory_size = fsc_memory_size
    quotient = paynt.parser.sketch.Sketch.load_sketch(
        sketch_path, properties_path, use_exact=exact
    )

    # print all python properties of quotient
    family = quotient.family

    if isinstance(quotient, paynt.quotient.pomdp_family.PomdpFamilyQuotient):
        print(quotient.observation_to_actions)

    s = z3.Solver()

    constraint.solver_settings(s)

    bit_nums = set()

    num_bits = (
        max(
            [
                math.ceil(math.log2(len(family.hole_options(hole)) + 1))
                for hole in range(family.num_holes)
            ]
        )
        + 1
    )

    variables = []

    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        bit_nums.add(num_bits)
        var = z3.BitVec(name, num_bits)
        variables.append(var)

    def variables_in_ranges(variables):
        statement = []
        for hole in range(family.num_holes):
            options = family.hole_options(hole)
            # it gets guaranteed by paynt that this is actually the range
            # (these are just the indices, not the actual values in the final model :)
            assert min(options) == 0
            var = variables[hole]
            statement.append(z3.UGE(var, z3.BitVecVal(min(options), num_bits)))
            statement.append(z3.ULE(var, z3.BitVecVal(max(options), num_bits)))
        return z3.And(*statement)

    # Create the valid(...) function
    f = z3.PropagateFunction("valid", *[x.sort() for x in variables], z3.BoolSort())

    s.add(constraint.build_constraint(f, variables, variables_in_ranges))

    # add test z3 constraints
    # s.add(variables[0] + variables[1] == variables[2])
    # s.add(variables[0] == 0)
    # s.add(variables[1] == 0)

    p = Mole(
        s,
        variables,
        quotient,
        draw_image=(image or search_space_test),
        considered_counterexamples=considered_counterexamples,
    )
    # p.register_variables(variables)
    model = None
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            # if var has as_long attribute
            if hasattr(model.eval(var), "as_long"):
                new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # re-check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
        constraint.show_result(model, s)
    else:
        print("unsat")
    print(f"Considered {p.considered_models} models")
    if print_reasons:
        print(f"Reasons:")
        for r in p.reasons:
            print(f"  {r}")
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
