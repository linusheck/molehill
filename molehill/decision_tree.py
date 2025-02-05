"""Decision tree business."""

import z3


def piecewise_select(array, z3_int):
    """Select an element of an array based on a z3 integer."""
    return z3.Sum([z3.If(z3_int == i, array[i], 0) for i in range(len(array))])

def build_decision_tree(variables, tree_depth):
    # variables have names of the form
    # A([picked0=1       & picked1=0     & picked2=1     & picked3=1     & picked4=0     & picked5=1     & picked6=1     & x=3   & y=2],0
    first_variable_name = str(variables[0])
    property_names = [
        x.strip().split("=")[0]
        for x in first_variable_name[
            first_variable_name.find("[") + 1 : first_variable_name.find("]")
        ].split("&")
    ]
    num_properties = len(property_names)

    # create a function
    max_action_size = max([x.size() for x in variables])
    decision_func = z3.Function("decision", *[z3.IntSort()] * num_properties, z3.BitVecSort(max_action_size))

    constraints = []

    num_nodes = 2 ** tree_depth - 1
    
    leaf_values = [z3.BitVec(f"leaf_{i}", max_action_size) for i in range(num_nodes + 1)]

    # make weight nodes for constraints
    node_property = []
    node_constants = []
    for i in range(num_nodes):
        # weight per variable
        node_weights = [z3.Real(f"node_{i}_prop_{j}") for j in range(num_properties)]
        node_property.append(node_weights)
        node_constants.append(z3.Real(f"const_{i}"))

    def decision_at_node(node: int, properties):
        return z3.Sum([properties[i] * node_property[node][i] for i in range(num_properties)]) >= node_constants[node]

    def traverse_tree(node: int, properties: list[int]):
        if node >= num_nodes:
            return leaf_values[node - num_nodes]
        else:
            left = traverse_tree(2 * node + 1, properties)
            right = traverse_tree(2 * node + 2, properties)
            return z3.If(decision_at_node(node, properties), left, right)

    decision_variables = [z3.Int(f"decision_{i}") for i in range(num_properties)]
    constraints.append(z3.ForAll(decision_variables, traverse_tree(0, decision_variables) == decision_func(*decision_variables)))

    for variable in variables:
        print(variable)
        variable_name = str(variable)
        property_values = [
            int(x.strip().split("=")[1])
            for x in variable_name[
                variable_name.find("[") + 1 : variable_name.find("]")
            ].split("&")
        ]
        print(property_values)
        constraints.append(variable == decision_func(*property_values))
    print(constraints)

    return constraints

def draw_tree(model):
    print(model)
