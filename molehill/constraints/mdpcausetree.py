"""A classic decision tree."""

import z3
from molehill.constraints import Constraint
from itertools import chain
import os


def piecewise_select(array, z3_int):
    """Select an element of an array based on a z3 integer."""
    sum_expr = array[0]
    for i in range(1, len(array)):
        sum_expr = z3.If(z3_int == i, array[i], sum_expr)
    return sum_expr


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


class MDPCauseTree(Constraint):
    def __init__(self, robust=False):
        super().__init__()
        self.variables = None
        self.policy_vars = None
        self.labels = None
        self.label_to_index = None
        self.left_child_ranges = None
        self.right_child_ranges = None

    def register_arguments(self, argument_parser):
        argument_parser.add_argument(
            "--pictures",
            type=str,
            help="Path to write tree pictures to.",
            default="pictures",
        )
        argument_parser.add_argument(
            "--nodes",
            "--tree-nodes",
            type=int,
            help="Number of enabled nodes in the tree.",
        )
        argument_parser.add_argument(
            "--relax",
            help="Relax the constraint to allow for * labels to be used when the decision tree's value is out of range.",
            action="store_true",
            default=False,
        )
        argument_parser.add_argument(
            "--no-minimality",
            help=(
                "Disable minimality constraints that push for HP-minimal causes. "
            ),
            action="store_true",
            default=False,
        )


    def build_constraint(self, function, variables, variables_in_ranges, **args):
        self.variables = variables
        num_nodes = self.args.nodes

        num_bits = max([x.size() for x in variables])

        policy_indices = list(range(len(variables)))
        policy_vars = [variables[i] for i in policy_indices]
        self.policy_vars = policy_vars

        assert "family" in args, "Family must be provided to MDPCause."
        assert "project_path" in args, "Project path must be provided to MDPCause."

        # Collect all action labels and put them into an order
        labels = list(
            dict.fromkeys(
                chain(
                    *[args["family"].hole_to_option_labels[i] for i in policy_indices]
                )
            )
        ) + ["*"] # special whatever label maps to max(actions)+1
        print("Labels:", labels)
        label_to_index = {label: i for i, label in enumerate(labels)}
        self.labels = labels
        self.label_to_index = label_to_index
        hole_to_label_indices = []
        assert 2**num_bits > len(labels)

        # Check that the available action labels of policy vars are consistent
        for i in policy_indices:
            hole_to_label_indices.append(
                [
                    label_to_index[label]
                    for label in args["family"].hole_to_option_labels[i]
                ] + [label_to_index["*"]]
            )
        
        # parse values.csv to get variable-value pairs
        variable_value_pairs_orig = []
        with open(os.path.join(args["project_path"], "values.csv"), "r") as f:
            header = f.readline().strip().split(",")
            for line in f:
                values = line.strip().split(",")
                variable_value_pairs_orig.append(
                    {header[i]: float(values[i]) for i in range(len(header))}
                )

        variable_value_pairs = []
        
        quotient = args["quotient"]
        choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
        transition_matrix = quotient.quotient_mdp.transition_matrix
        
        # go through transition matrix 
        for state in range(quotient.quotient_mdp.nr_states):
            first_row = transition_matrix.get_rows_for_group(state)[0]
            if len(choice_to_hole_options[first_row]) == 0:
                pass
            else:
                variable_value_pairs.append(variable_value_pairs_orig[state])

        # Use filtered variable_value_pairs
        property_names = list(variable_value_pairs[0].keys())
        self.property_names = property_names
        num_properties = len(property_names)

        property_ranges = [(float("inf"), float("-inf")) for _ in range(num_properties)]
        for var_values in variable_value_pairs:
            for i, prop_name in enumerate(property_names):
                val = var_values[prop_name]
                property_ranges[i] = (
                    min(property_ranges[i][0], val),
                    max(property_ranges[i][1], val),
                )

        constraints = []

        decision_functions = []
        for i in range(num_nodes):
            decision_functions.append(
                z3.Function(
                    f"decision_{i}",
                    *[z3.RealSort()] * num_properties,
                    z3.BitVecSort(num_bits),
                )
            )

        self.left_child_ranges = [
            [j for j in range(i + 1, min(2 * (i + 1), num_nodes)) if j % 2 == 1]
            for i in range(num_nodes)
        ]
        self.right_child_ranges = [
            [j for j in range(i + 2, min(2 * (i + 1) + 1, num_nodes)) if j % 2 == 0]
            for i in range(num_nodes)
        ]

        node_constants = []
        property_indices = []
        node_is_leaf = []
        left_children = []
        right_children = []

        for i in range(num_nodes):
            is_leaf = z3.Bool(f"leaf_{i}")
            node_is_leaf.append(is_leaf)

            constant_var = z3.BitVec(f"const_{i}", num_bits)
            node_constants.append(constant_var)
            
            threshold_var = z3.Real(f"threshold_{i}")

            prop_index = z3.Int(f"prop_index_{i}")
            constraints.append(prop_index >= 0)
            constraints.append(prop_index < num_properties)
            property_indices.append(prop_index)

            constraints.append(z3.UGE(constant_var, 0))
            constraints.append(
                z3.If(
                    is_leaf,
                    z3.ULT(constant_var, len(labels)),
                    z3.And(
                        threshold_var
                        <= piecewise_select(
                            [z3.RealVal(x[1]) for x in property_ranges],
                            prop_index,
                        ),
                        threshold_var
                        >= piecewise_select(
                            [z3.RealVal(x[0]) for x in property_ranges],
                            prop_index,
                        ),
                    ),
                )
            )

            left_child = z3.Int(f"left_{i}")
            left_children.append(left_child)
            right_child = z3.Int(f"right_{i}")
            right_children.append(right_child)

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

            all_property_values = []
            for variable_values_dict in variable_value_pairs:
                tmp_values = []
                for name in property_names:
                    tmp_values.append(variable_values_dict[name])
                all_property_values.append(tmp_values)

            for values in all_property_values:
                prop_vals = [z3.RealVal(v) for v in values]
                constraints.append(
                    z3.If(
                        is_leaf,
                        decision_functions[i](*prop_vals) == constant_var,
                        z3.If(
                            piecewise_select(prop_vals, prop_index) >= threshold_var,
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

        constraints.append(z3.Sum(node_is_leaf) == (num_nodes + 1) // 2)

        for i in range(1, num_nodes):
            left_children_ranges = [
                j for j in range(num_nodes) if i in self.left_child_ranges[j]
            ]
            right_children_ranges = [
                j for j in range(num_nodes) if i in self.right_child_ranges[j]
            ]
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

        for i, variable in enumerate(policy_vars):
            values_dict = variable_value_pairs[i]
            property_values_z3 = [z3.RealVal(values_dict[p]) for p in property_names]

            label_range = args["family"].hole_to_option_labels[policy_indices[i]] + ["*"]
            
            if label_range == labels:
                constraints.append(variable == decision_functions[0](*property_values_z3))
            else:
                label_indices = [label_to_index[label] for label in label_range]
                x = decision_functions[0](*property_values_z3)
                for index, label_index in enumerate(label_indices):
                    if self.args.relax:
                        if label_index != label_to_index["*"]:
                            constraints.append((variable == index) == (x == label_index))
                        else:
                            constraints.append((variable == index) == z3.Or(x == label_index, x == label_to_index["*"]))
                    else:
                        constraints.append((variable == index) == (x == label_index))

        arguments = variables

        var_in_range_statement = variables_in_ranges(arguments)
        constraints += [function(*arguments), var_in_range_statement]

        return constraints



    def show_result(self, model, _solver, **args):
        from anytree import Node
        from anytree.exporter import UniqueDotExporter

        property_names = self.property_names

        num_nodes = self.args.nodes
        num_bits = max([x.size() for x in self.policy_vars])

        is_leaf = [model[z3.Bool(f"leaf_{i}")] for i in range(num_nodes)]
        left_children = [model[z3.Int(f"left_{i}")] for i in range(num_nodes)]
        right_children = [model[z3.Int(f"right_{i}")] for i in range(num_nodes)]
        node_constants = [
            model[z3.BitVec(f"const_{i}", num_bits)] for i in range(num_nodes)
        ]
        node_thresholds = [
            model[z3.Real(f"threshold_{i}")] for i in range(num_nodes)
        ]
        node_properties = [model[z3.Int(f"prop_index_{i}")] for i in range(num_nodes)]

        # a bit of code duplication, sorry
        def build_anytree(node_index):
            if is_leaf[node_index]:
                if "family" in args:
                    # get action names from family
                    if node_constants[node_index].as_long() >= len(self.labels):
                        # This can happen if this node is never visited
                        return Node("noop")
                    else:
                        return Node(
                            self.labels[node_constants[node_index].as_long()],
                        )
                return Node(node_constants[node_index])
            else:
                i = node_index
                val = node_thresholds[i]
                val_str = val.as_decimal(3) if hasattr(val, "as_decimal") else str(val)
                # remove trailing zeros
                if "?" in val_str:
                    val_str = val_str.replace("?", "")
                
                calc = (
                    property_names[node_properties[i].as_long()]
                    + f" >= {val_str}?"
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
        if self.args.pictures is None:
            return
        picture_path = self.args.pictures
        os.makedirs(picture_path, exist_ok=True)

        UniqueDotExporter(root).to_dotfile(picture_path + "/tree.dot")
        UniqueDotExporter(root).to_picture(picture_path + "/tree.png")
