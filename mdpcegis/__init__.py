import paynt.synthesizer
import paynt.synthesizer.conflict_generator
import paynt.verification
import paynt.verification.property
import z3
import paynt.parser.sketch
import sys
import math

from mdpcegis.curve_drawer import draw_curve
from mdpcegis.plugin import SearchMarkovChain

def example1(project_path):
    sketch_path = f"{project_path}/sketch.templ"
    properties_path = f"{project_path}/sketch.props"
    quotient = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)

    # print all python properties of quotient
    family = quotient.family

    quotient.build(family)
    s = z3.Solver()

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

    # make z3 simple solver
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
        print(f"Considered {p.considered_models} models")
    else:
        print("unsat")

    draw_curve(num_bits, variables, s, p, model)

if __name__ == "__main__":
    example1(sys.argv[1])
