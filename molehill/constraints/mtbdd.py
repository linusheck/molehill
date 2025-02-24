"""A function with n-bit choices."""

import z3
import math
from molehill.constraints import Constraint

def bit2bool(var, i):
    return z3.BoolRef(z3.Z3_mk_bit2bool(var.ctx.ref(), i, var.as_ast()))

def get_property_names(variable_name):
    return [
        x.strip().split("=")[0].replace("!", "")
        for x in variable_name[
            variable_name.find("[") + 1 : variable_name.find("]")
        ].split("&")
    ]

def get_property_values(variable_name):
    return [
        int(x.strip().split("=")[1]) if "=" in x else (0 if x.strip()[0] == "!" else 1)
        for x in variable_name[
            variable_name.find("[") + 1 : variable_name.find("]")
        ].split("&")
    ]

class MTBDD(Constraint):
    def __init__(self):
        self.decision_func = None
        self.property_names = None
        self.node_property = None
        self.node_constants = None
    
    def register_arguments(self, argument_parser):
        argument_parser.add_argument(
            "--num_nodes", type=int, default=3, help="Number of nodes in the decision tree"
        )

    def build_constraint(self, variables, args):
        num_nodes = args.num_nodes
        num_bits = variables[0].size()
        assert all(
            [x.size() == num_bits for x in variables]
        ), "Only works for variables of the same size"
        # variables have names of the form
        # A([picked0=1       & picked1=0     & picked2=1     & picked3=1     & picked4=0     & picked5=1     & picked6=1     & x=3   & y=2],0
        first_variable_name = str(variables[0])
        if "A([" not in first_variable_name:
            raise ValueError("Variables must have properties (e.g., generated from POMDPs.).")
        property_names = get_property_names(first_variable_name)
        self.property_names = property_names
        num_properties = len(property_names)

        property_ranges = [(1e6, -1e6) for _ in range(num_properties)]
        for variable in variables:
            property_values = get_property_values(str(variable))
            for i in range(num_properties):
                property_ranges[i] = (
                    min(property_ranges[i][0], property_values[i]),
                    max(property_ranges[i][1], property_values[i]),
                )

        # create a function
        decision_func = z3.Function(
            "decision", z3.BitVecSort(num_nodes), z3.BitVecSort(num_bits)
        )
        self.decision_func = decision_func

        constraints = []

        # make weight nodes for constraints
        node_property = []
        node_constants = []
        for i in range(num_nodes):
            # weight per variable
            prop_index = z3.BitVec(
                f"node_{i}", math.ceil(math.log2(num_properties)) + 1
            )

            # prop index must be in range
            constraints.append(z3.ULT(prop_index, num_properties))

            node_property.append(prop_index)
            constant_var = z3.Int(f"const_{i}")
            node_constants.append(constant_var)
            constraints.append(constant_var >= 0)
            constraints.append(constant_var <= max(x[1] for x in property_ranges))

            # break symmetry :)
            if i > 0:
                constraints.append(z3.UGE(node_property[i], node_property[i - 1]))

        self.node_property = node_property
        self.node_constants = node_constants

        # if one_node_per_decision:
        #     tree_enumeration = build_tree_enumeration(num_nodes, decision_func)
        #     print(tree_enumeration)
        #     constraints += tree_enumeration

        def decision_at_node(node: int, properties):
            return (
                z3.Sum(
                    [
                        z3.If(
                            node_property[node]
                            == z3.BitVecVal(
                                i, math.ceil(math.log2(num_properties)) + 1
                            ),
                            properties[i],
                            0,
                        )
                        for i in range(num_properties)
                    ]
                )
                >= node_constants[node]
            )

        for variable in variables:
            property_values = get_property_values(str(variable))
            # print("Property values are", property_values, "for variable", variable)
            decisions = [decision_at_node(i, property_values) for i in range(num_nodes)]
            # decisions = [z3.Bool(f"decision_{variable}_{i}") for i in range(num_nodes)]

            # print("Decisions are", decisions)
            decision_bits = [
                z3.If(dec, z3.BitVecVal(1, num_nodes), z3.BitVecVal(0, num_nodes))
                for dec in decisions
            ]
            decision_sequence = decision_bits[0]
            for i in range(1, num_nodes):
                decision_sequence = (decision_sequence << 1) | decision_bits[i]
            constraints.append(variable == decision_func(decision_sequence))
        return constraints

    def generate_mtbdd(self, function, decision):
        def build(sub_function):
            if len(sub_function) == 1:
                return sub_function[""]
            else:
                left = build({x[1:]: y for x, y in sub_function.items() if x[0] == "0"})
                right = build(
                    {x[1:]: y for x, y in sub_function.items() if x[0] == "1"}
                )
                if left == right:
                    return [left]
                return [left, right]

        def generate_dot(mtbdd):
            dot = "digraph G {rankdir=TB;"

            def traverse(node, node_id, depth):
                if isinstance(node, int):
                    assert depth == -1
                    return f'{node_id} [label="{node}"];\n'
                elif len(node) == 1:
                    return traverse(node[0], node_id, depth - 1)
                else:
                    d = ""
                    d += f'{node_id} [label="{decision[len(decision) - depth - 1]}"];\n'
                    d += f"{node_id} -> {2 * node_id + 1} [style=dashed];\n"
                    d += f"{node_id} -> {2 * node_id + 2};\n"
                    return (
                        d
                        + traverse(node[0], 2 * node_id + 1, depth - 1)
                        + traverse(node[1], 2 * node_id + 2, depth - 1)
                    )

            dot += traverse(mtbdd, 0, len(decision) - 1)
            dot += "}"
            return dot

        mtbdd = build(function)
        with open("mtbdd.dot", "w", encoding="utf-8") as f:
            f.write(generate_dot(mtbdd))

    def show_result(self, model, _solver):
        decisions = []
        for i in range(len(self.node_constants)):
            property_name = self.property_names[model[self.node_property[i]].as_long()]
            decision = f"{property_name} <= {model[self.node_constants[i]]}?"
            decisions.append(decision)
            print(f"Decision {i}: {decision}")

        function = {}
        for i in range(0, 2 ** len(self.node_constants)):
            decision_bits = "".join(
                [str(x) for x in bin(i)[2:].zfill(len(self.node_constants))]
            )
            result = model.eval(
                self.decision_func(z3.BitVecVal(i, len(self.node_constants)))
            ).as_long()
            print(f"{decision_bits} -> {result}")
            function[decision_bits] = result
        self.generate_mtbdd(function, decisions)
        return


# Dead code that I tried out


# def build_tree_enumeration(num_nodes, function):
#     # Build tree enumeration with num_nodes nodes
#     constraints = []
#     indicator_bits = math.ceil(math.log2(num_nodes * 2))
#     variables = []
#     for i in range(num_nodes - 1):
#         variable = z3.BitVec(f"indicator_{i}", indicator_bits)
#         variables.append(variable)
#         constraints.append(z3.ULT(variable, z3.BitVecVal(num_nodes * 2 - 2, indicator_bits)))
#         # variables are strictly ordered
#         if i > 0:
#             constraints.append(z3.UGT(variable, variables[i - 1]))
    
#     def make_sum(to):
#         return z3.Sum(
#                 [
#                     z3.If(
#                         z3.ULT(x, z3.BitVecVal(to, indicator_bits)),
#                         z3.BitVecVal(1, indicator_bits),
#                         z3.BitVecVal(0, indicator_bits),
#                     )
#                     for x in variables
#                 ]
#             )
    
#     def table(x):
#         return z3.Or(
#             [x == z3.BitVecVal(i, indicator_bits) for i in range(num_nodes * 2)]
#         )

#     for i in range(1, num_nodes):
#         # there are at least i numbers smaller than 2*i
#         constraints.append(
#             z3.UGE(make_sum(2*i),
#              z3.BitVecVal(i, indicator_bits))
#         )


#     x = z3.BitVec("x", num_nodes)
#     mask = z3.BitVec("mask", num_nodes)
#     def mask_constraints(x, mask):
#         result = []
#         # forall bit vectors x (Z3 quantifier)
#         # forall i (for loop)
#         # if mask[i] and t[2i] and not x[i]
#         # then mask[sums[2i]]
#         # if mask[i] and t[2i+1] and x[i]
#         # then mask[sums[2i+1]]
#         # (note: t[j] == (sums[j] == sums[j+1]))
#         # and f(x & mask) == f(x)
#         for i in range(num_nodes):
#             mask_i = bit2bool(mask, i)
#             x_i = bit2bool(x, i)
#             t_2i = table(2*i)
#             t_2ip1 = table(2*i+1)
#             sums_2i = make_sum(2*i)
#             sums_2ip1 = make_sum(2*i+1)
#             result.append(
#                 z3.Implies(
#                     z3.And(mask_i, t_2i, z3.Not(x_i)),
#                     z3.Or([z3.And(j == sums_2i, bit2bool(mask, j)) for j in range(num_nodes)])
#                 )
#             )
#             result.append(
#                 z3.Implies(
#                     z3.And(mask_i, t_2ip1, x_i),
#                     z3.Or([z3.And(j == sums_2ip1, bit2bool(mask, j)) for j in range(num_nodes)])
#                 )
#             )
#         result.append(function(x & mask) == function(x))
#         return z3.And(*result)
#     constraints.append(z3.ForAll([x], z3.Exists([mask], mask_constraints(x, mask))))
#     return constraints
