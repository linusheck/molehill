"""A classic decision tree."""

import z3
from molehill.constraints import Constraint
from itertools import product


def piecewise_select(array, z3_int):
    """Select an element of an array based on a z3 integer."""
    return z3.Sum([z3.If(z3_int == i, array[i], 0) for i in range(len(array))])


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


class DecisionTree(Constraint):
    def __init__(self, robust=False):
        super().__init__()
        self.variables = None
        self.policy_vars = None
        self.robust = robust

    def register_arguments(self, argument_parser):
        argument_parser.add_argument(
            "--picture-path",
            type=str,
            help="Path to write tree picture to.",
            default="tree.png",
        )
        argument_parser.add_argument(
            "--nodes",
            type=int,
            help="Number of enabled nodes in the tree.",
        )
        if self.robust:
            argument_parser.add_argument(
                "--forall",
                type=str,
                help="Infix of the forall variables E.g: 'P1 P3' means all variables that contain either P1 or P3.",
                default="sketch_hole",
            )

    def build_constraint(self, function, variables, variables_in_ranges, **args):
        self.variables = variables
        num_nodes = self.args.nodes

        forall_variables = []
        forall_indices = []
        if self.robust:
            # build forall constraint
            forall_indices = [
                i
                for i, var in enumerate(variables)
                if any([x in str(var) for x in self.args.forall.split(" ")])
            ]
            forall_variables = [variables[i] for i in forall_indices]
            if len(forall_variables) == 0:
                raise ValueError("No variables found with the given pattern.")

        num_bits = max([x.size() for x in variables])

        policy_indices = list(range(len(variables)))
        if self.robust:
            # remove the forall variables from the policy indices
            for i in forall_indices:
                policy_indices.remove(i)
        policy_vars = [variables[i] for i in policy_indices]
        self.policy_vars = policy_vars

        # Check that the available action labels of policy vars are consistent
        if "family" in args:
            labels = args["family"].hole_to_option_labels[policy_indices[0]]
            for i in policy_indices:
                print(args["family"].hole_to_option_labels[i], labels)
                if args["family"].hole_to_option_labels[i] != labels:
                    raise ValueError(
                        f"The available action labels of the policy variables are inconsistent ({labels} vs {args['family'].hole_to_action_labels[i]})."
                    )

        # variables have names of the form
        # A([picked0=1       & picked1=0     & picked2=1     & picked3=1     & picked4=0     & picked5=1     & picked6=1     & x=3   & y=2],0
        first_variable_name = str(policy_vars[0])
        if "A([" not in first_variable_name:
            raise ValueError(
                "Variables must have properties (e.g., generated from POMDPs.)."
            )
        property_names = get_property_names(first_variable_name)
        num_properties = len(property_names)

        property_ranges = [(1e6, -1e6) for _ in range(num_properties)]
        for variable in policy_vars:
            property_values = get_property_values(str(variable))
            for i in range(num_properties):
                property_ranges[i] = (
                    min(property_ranges[i][0], property_values[i]),
                    max(property_ranges[i][1], property_values[i]),
                )

        constraints = []

        # create a function for each node
        decision_functions = []
        for i in range(num_nodes):
            decision_functions.append(
                z3.Function(
                    f"decision_{i}",
                    *[z3.BitVecSort(num_bits)] * num_properties,
                    z3.BitVecSort(num_bits),
                )
            )

        # Left child is in range even([i+1, min(2i, num_nodes-1)])
        # Right child is in range odd([i+2, min(2i+1, num_nodes)])
        self.left_child_ranges = [
            [j for j in range(i + 1, min(2 * (i + 1), num_nodes)) if j % 2 == 1]
            for i in range(num_nodes)
        ]
        self.right_child_ranges = [
            [j for j in range(i + 2, min(2 * (i + 1) + 1, num_nodes)) if j % 2 == 0]
            for i in range(num_nodes)
        ]

        # make weight nodes for constraints
        node_constants = []
        property_indices = []
        node_is_leaf = []
        left_children = []
        right_children = []

        forall_statements = []

        for i in range(num_nodes):
            # The constant of a node
            constant_var = z3.BitVec(f"const_{i}", num_bits)
            node_constants.append(constant_var)

            constraints.append(z3.UGE(constant_var, 0))
            constraints.append(
                z3.ULE(constant_var, max([x[1] for x in property_ranges]))
            )

            # The property index of a node
            prop_index = z3.Int(f"prop_index_{i}")
            # Must be in range
            constraints.append(prop_index >= 0)
            # print(num_properties)
            constraints.append(prop_index < num_properties)
            property_indices.append(prop_index)
            # Is this node a leaf?
            is_leaf = z3.Bool(f"leaf_{i}")
            node_is_leaf.append(is_leaf)

            left_child = z3.Int(f"left_{i}")
            left_children.append(left_child)
            right_child = z3.Int(f"right_{i}")
            right_children.append(right_child)
            # If this node is a leaf, the left and right children must be 0

            constraints.append(
                z3.If(
                    is_leaf,
                    left_child == 0,
                    left_child <= len(self.left_child_ranges[i]),
                )
            )
            constraints.append(
                z3.If(
                    is_leaf,
                    right_child == 0,
                    right_child <= len(self.right_child_ranges[i]),
                )
            )
            constraints.append(z3.Implies(is_leaf, prop_index == 0))

            value_domains = [range(lo, hi + 1) for lo, hi in property_ranges]
            # number of values in the product iterator:
            num_values = 1
            for lo, hi in property_ranges:
                num_values *= hi - lo + 1
            if num_values < 10000:
                for values in product(*value_domains):
                    prop_vals = [z3.BitVecVal(v, num_bits) for v in values]
                    constraints.append(
                        z3.If(
                            is_leaf,
                            decision_functions[i](*prop_vals) == constant_var,
                            z3.If(
                                z3.UGE(
                                    piecewise_select(prop_vals, prop_index),
                                    constant_var,
                                ),
                                z3.Or(
                                    *[
                                        z3.And(
                                            left_child == j,
                                            decision_functions[i](*prop_vals)
                                            == decision_functions[
                                                self.left_child_ranges[i][j]
                                            ](*prop_vals),
                                        )
                                        for j in range(len(self.left_child_ranges[i]))
                                    ]
                                ),
                                z3.Or(
                                    *[
                                        z3.And(
                                            right_child == j,
                                            decision_functions[i](*prop_vals)
                                            == decision_functions[
                                                self.right_child_ranges[i][j]
                                            ](*prop_vals),
                                        )
                                        for j in range(len(self.right_child_ranges[i]))
                                    ]
                                ),
                            ),
                        )
                    )
            else:
                print(
                    f"Too many values ({num_values}) for explicit tree constraints, using forall quantification."
                )
                # Symbolically forall-quantify over the values (too many to enumerate)
                property_vars = [
                    z3.BitVec(f"prop_{i}", num_bits) for i in range(num_properties)
                ]
                forall_statements.append(
                    z3.ForAll(
                        property_vars,
                        z3.If(
                            is_leaf,
                            decision_functions[i](*property_vars) == constant_var,
                            z3.If(
                                z3.UGE(
                                    piecewise_select(property_vars, prop_index),
                                    constant_var,
                                ),
                                z3.And(
                                    [
                                        z3.If(
                                            left_child == j,
                                            decision_functions[i](*property_vars)
                                            == decision_functions[
                                                self.left_child_ranges[i][j]
                                            ](*property_vars),
                                            True,
                                        )
                                        for j in range(len(self.left_child_ranges[i]))
                                    ]
                                ),
                                z3.And(
                                    [
                                        z3.If(
                                            right_child == j,
                                            decision_functions[i](*property_vars)
                                            == decision_functions[
                                                self.right_child_ranges[i][j]
                                            ](*property_vars),
                                            True,
                                        )
                                        for j in range(len(self.right_child_ranges[i]))
                                    ]
                                ),
                            ),
                        ),
                    )
                )

        # each tree has (num_nodes+1) / 2 leaves
        constraints.append(z3.Sum(node_is_leaf) == (num_nodes + 1) // 2)
        # each node, except 0, must have a parent, that is before it

        for i in range(1, num_nodes):
            # identify the nodes that have i in left_child_ranges or right_child_ranges
            left_children_ranges = [
                j for j in range(num_nodes) if i in self.left_child_ranges[j]
            ]
            right_children_ranges = [
                j for j in range(num_nodes) if i in self.right_child_ranges[j]
            ]
            # i is left_child of one of the left_children or right_child of one of the right_children
            parent_constraint = z3.Or(
                *[
                    z3.And(
                        left_children[x] == self.left_child_ranges[x].index(i),
                        z3.Not(node_is_leaf[x]),
                    )
                    for x in left_children_ranges
                    if i in self.left_child_ranges[x]
                ]
                + [
                    z3.And(
                        right_children[x] == self.right_child_ranges[x].index(i),
                        z3.Not(node_is_leaf[x]),
                    )
                    for x in right_children_ranges
                    if i in self.right_child_ranges[x]
                ]
            )
            constraints.append(parent_constraint)

        for variable in policy_vars:
            property_values = get_property_values(str(variable))
            constraints.append(variable == decision_functions[0](*property_values))

        arguments = variables

        var_in_range_statement = variables_in_ranges(arguments)
        if self.robust:
            forall_constraint = z3.And(
                var_in_range_statement,
                z3.ForAll(
                    *[forall_variables],
                    z3.Implies(var_in_range_statement, function(*arguments)),
                ),
            )
            constraints += [forall_constraint]
        else:
            constraints += [function(*arguments), var_in_range_statement]
        return constraints

    def show_result(self, model, _solver, **args):
        from anytree import Node
        from anytree.exporter import UniqueDotExporter

        first_variable_name = str(self.policy_vars[0])
        property_names = get_property_names(first_variable_name)

        num_nodes = self.args.nodes
        num_bits = max([x.size() for x in self.policy_vars])

        is_leaf = [model[z3.Bool(f"leaf_{i}")] for i in range(num_nodes)]
        left_children = [model[z3.Int(f"left_{i}")] for i in range(num_nodes)]
        right_children = [model[z3.Int(f"right_{i}")] for i in range(num_nodes)]
        node_constants = [
            model[z3.BitVec(f"const_{i}", num_bits)] for i in range(num_nodes)
        ]
        node_properties = [model[z3.Int(f"prop_index_{i}")] for i in range(num_nodes)]

        # a bit of code duplication, sorry
        def build_anytree(node_index):
            if is_leaf[node_index]:
                if "family" in args:
                    # get action names from family
                    return Node(
                        args["family"].hole_to_option_labels[
                            self.variables.index(self.policy_vars[0])
                        ][node_constants[node_index].as_long()]
                    )
                return Node(node_constants[node_index])
            else:
                i = node_index
                print(node_properties)
                calc = (
                    property_names[node_properties[i].as_long()]
                    + f" >= {node_constants[i]}?"
                )
                node = Node(calc)

                left_child = self.left_child_ranges[i][
                    left_children[node_index].as_long()
                ]
                right_child = self.right_child_ranges[i][
                    right_children[node_index].as_long()
                ]
                node.children = [
                    build_anytree(right_child),
                    build_anytree(left_child),
                ]
                return node

        root = build_anytree(0)
        if self.args.picture_path is not None:
            UniqueDotExporter(root).to_picture(self.args.picture_path)
            print("Tree written to", self.args.picture_path)
