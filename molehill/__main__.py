import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import sys
import math

# from molehill.curve_drawer import draw_curve
from molehill.plugin import SearchMarkovChain

def example1(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)

    # print all python properties of quotient
    family = quotient.family

    quotient.build(family)
    s = z3.Solver()

    # set random phase selection
    s.set("phase_selection", 5)

    variables = []
    # create variables
    num_bits = max([math.ceil(math.log2(max(family.hole_options(hole)) + 1)) for hole in range(family.num_holes)]) + 1
    for hole in range(family.num_holes):
        name = family.hole_name(hole)
        options = family.hole_options(hole)
        var = z3.BitVec(name, num_bits)
        variables.append(var)
        # TODO hole options of full family should be a sorted vector of indices that is continous
        s.add(z3.And(var >= z3.BitVecVal(min(options), num_bits), var <= z3.BitVecVal(max(options), num_bits)))

    # add test z3 constraints
    # # M_0_1=0, M_1_1=0, M_2_1=2, M_3_1=2, P_0_1=4
    # s.add(variables[0] == 2)
    # s.add(variables[1] == 1)
    # s.add(variables[2] == 1)
    # s.add(variables[3] == 3)
    # s.add(variables[4] == 1)
    # s.add(variables[5] == 3)
    # s.add(variables[6] == 2)
    #[[0, 3, 4]]

    p = SearchMarkovChain(s, quotient)
    p.register_variables(variables)
    print(variables)
    model = None
    if s.check() == z3.sat:
        print("sat")
        model = s.model()
        new_family = quotient.family.copy()
        new_family.add_parent_info(quotient.family)
        for hole in range(new_family.num_holes):
            var = variables[hole]
            new_family.hole_set_options(hole, [model.eval(var).as_long()])
        # check DTMC
        quotient.build(new_family)
        mdp = new_family.mdp
        prop = quotient.specification.all_properties()[0]
        result = mdp.model_check_property(prop)
        print(f"Found {new_family} with value {result}")
    else:
        print("unsat")
    print(f"Considered {p.considered_models} models")
    print(f"MDP checking had {p.mdp_fails_and_wins[0]} fails and {p.mdp_fails_and_wins[1]} wins ({round(p.mdp_fails_and_wins[1] / sum(p.mdp_fails_and_wins) * 100, 1)}% wins)")

    # draw_curve(num_bits, variables, s, p, model)

if __name__ == "__main__":
    example1(sys.argv[1])
