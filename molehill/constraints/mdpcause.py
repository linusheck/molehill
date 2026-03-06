"""A rectangle-rule-list cause for an MDP.

Each rule is: IF prop_0 in [lo, hi] AND ... THEN action (ignoring inactive properties)
Rules are checked in order; first match wins. If nothing matches → '*'.

Features included:
  1. Integer Discretization: Bounds are indices over sorted unique observed values.
  2. Derived Activity: prop_active is purely derived from whether bounds are non-trivial.
  3. Sparsity/Cap: Hard cap on constraints per rule + optional soft penalty for active flags.
  4. Symmetry Breaking: Inactive rules pushed to bottom, identical rules forbidden,
     and lexicographical ordering for adjacent rules sharing the same label.
"""

import z3
from molehill.constraints import Constraint
from itertools import chain
import os


class MDPCause(Constraint):
    def __init__(self):
        super().__init__()
        self.variables = None
        self.policy_vars = None
        self.labels = None
        self.label_to_index = None
        self.property_names = None
        self.prop_sorted_vals = None

    def register_arguments(self, argument_parser):
        argument_parser.add_argument(
            "--pictures",
            type=str,
            help="Path to write rule output to.",
            default="pictures",
        )
        argument_parser.add_argument(
            "--rules",
            "--num-rules",
            type=int,
            help="Number of rectangle rules (excluding the default '*' fallback).",
        )
        argument_parser.add_argument(
            "--constraints-per-rule",
            type=int,
            default=None,
            help=(
                "Hard cap on the number of properties each rule may constrain. "
                "None means all properties are available."
            ),
        )
        argument_parser.add_argument(
            "--sparsity-weight",
            type=int,
            default=1,
            help="Soft-constraint weight penalizing each active property flag (default: 1).",
        )
        argument_parser.add_argument(
            "--relax",
            help=(
                "Relax the constraint to allow for * labels to be used when "
                "the decision value is out of range."
            ),
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

    # ------------------------------------------------------------------
    # Helper: encode "apply rule list to a concrete property vector"
    # ------------------------------------------------------------------
    def _apply_rules(
        self,
        prop_indices_concrete,
        rule_lows_idx,
        rule_highs_idx,
        rule_prop_active,
        rule_labels,
        num_rules,
        star_index,
        num_bits,
    ):
        num_properties = len(prop_indices_concrete)

        def rule_fires(r):
            per_prop = []
            for p in range(num_properties):
                prop_check = z3.And(
                    prop_indices_concrete[p] >= rule_lows_idx[r][p],
                    prop_indices_concrete[p] <= rule_highs_idx[r][p],
                )
                per_prop.append(
                    z3.If(rule_prop_active[r][p], prop_check, z3.BoolVal(True))
                )
            return z3.And(*per_prop)

        # Build right-folded chain from last rule up to first (rule 0 wins)
        result = z3.BitVecVal(star_index, num_bits)
        for r in reversed(range(num_rules)):
            result = z3.If(rule_fires(r), rule_labels[r], result)
        return result

    # ------------------------------------------------------------------
    def build_constraint(self, function, variables, variables_in_ranges, **args):
        self.variables = variables
        num_rules = self.args.rules

        num_bits = max([x.size() for x in variables])

        policy_indices = list(range(len(variables)))
        policy_vars = [variables[i] for i in policy_indices]
        self.policy_vars = policy_vars

        assert "family" in args, "Family must be provided to MDPCauseRectangles."
        assert "project_path" in args, "Project path must be provided."

        # ---- collect labels -------------------------------------------
        labels = list(
            dict.fromkeys(
                chain(
                    *[args["family"].hole_to_option_labels[i] for i in policy_indices]
                )
            )
        ) + ["*"]
        print("Labels:", labels)
        label_to_index = {label: i for i, label in enumerate(labels)}
        self.labels = labels
        self.label_to_index = label_to_index
        star_index = label_to_index["*"]

        assert 2**num_bits > len(labels)

        # ---- load values.csv and filter to controllable states --------
        variable_value_pairs_orig = []
        with open(os.path.join(args["project_path"], "values.csv"), "r") as f:
            header = f.readline().strip().split(",")
            for line in f:
                vals = line.strip().split(",")
                variable_value_pairs_orig.append(
                    {header[i]: float(vals[i]) for i in range(len(header))}
                )

        variable_value_pairs = []
        quotient = args["quotient"]
        choice_to_hole_options = quotient.coloring.getChoiceToAssignment()
        transition_matrix = quotient.quotient_mdp.transition_matrix

        for state in range(quotient.quotient_mdp.nr_states):
            first_row = transition_matrix.get_rows_for_group(state)[0]
            if len(choice_to_hole_options[first_row]) != 0:
                variable_value_pairs.append(variable_value_pairs_orig[state])

        property_names = list(variable_value_pairs[0].keys())
        self.property_names = property_names
        num_properties = len(property_names)

        # ---- Precompute sorted unique values per property -------------
        self.prop_sorted_vals = []
        for p, pname in enumerate(property_names):
            unique_vals = sorted(list(set(vv[pname] for vv in variable_value_pairs)))
            self.prop_sorted_vals.append(unique_vals)

        constraints = []
        self.soft_constraints = []

        # ----------------------------------------------------------------
        # Declare per-rule z3 variables using integer indices
        # ----------------------------------------------------------------
        rule_lows_idx    = []
        rule_highs_idx   = []
        rule_prop_active = []
        rule_labels      = []
        rule_active      = []

        for r in range(num_rules):
            lows_r   = [z3.Int(f"rule_{r}_lo_idx_{p}") for p in range(num_properties)]
            highs_r  = [z3.Int(f"rule_{r}_hi_idx_{p}") for p in range(num_properties)]
            label_r  = z3.BitVec(f"rule_{r}_label", num_bits)
            rule_active_r = z3.Bool(f"rule_{r}_active")

            prop_active_r = []
            for p in range(num_properties):
                max_idx = len(self.prop_sorted_vals[p]) - 1

                derived = z3.Bool(f"rule_{r}_prop_{p}_active")
                # Active iff bounds don't cover the full index range
                constraints.append(
                    derived == z3.Or(lows_r[p] > 0, highs_r[p] < max_idx)
                )
                prop_active_r.append(derived)

                # enforce valid index ranges
                constraints.append(lows_r[p] >= 0)
                constraints.append(highs_r[p] <= max_idx)
                constraints.append(lows_r[p] <= highs_r[p])
                
                # if inactive, perfectly pin to full range
                constraints.append(
                    z3.Implies(
                        z3.Not(derived),
                        z3.And(lows_r[p] == 0, highs_r[p] == max_idx),
                    )
                )

            rule_lows_idx.append(lows_r)
            rule_highs_idx.append(highs_r)
            rule_prop_active.append(prop_active_r)
            rule_labels.append(label_r)
            rule_active.append(rule_active_r)

            constraints.append(z3.UGE(label_r, 0))
            constraints.append(z3.ULT(label_r, star_index))

            # Optional hard cap on active flags
            k = self.args.constraints_per_rule
            if k is not None:
                constraints.append(
                    z3.Sum([z3.If(prop_active_r[p], 1, 0) for p in range(num_properties)]) <= k
                )

            # An active rule must constrain at least one property
            constraints.append(z3.Implies(rule_active_r, z3.Or(*prop_active_r)))
            
            # An inactive rule has no active properties
            constraints.append(
                z3.Implies(
                    z3.Not(rule_active_r),
                    z3.And(*[z3.Not(prop_active_r[p]) for p in range(num_properties)]),
                )
            )

            # Collect soft constraints to push for sparsity
            w = self.args.sparsity_weight
            for p in range(num_properties):
                self.soft_constraints.append((z3.Not(prop_active_r[p]), w))

        # --- SYMMETRY BREAKING ---
        
        # 1. Push inactive rules to the bottom (if rule r is inactive, r+1 must be inactive)
        for r in range(num_rules - 1):
            constraints.append(
                z3.Implies(z3.Not(rule_active[r]), z3.Not(rule_active[r+1]))
            )

        # 2. Lexicographical tie-breaking for adjacent rules with identical action labels
        #    (Prevents solver from pointlessly swapping two disjoint rules of the same color)
        for r in range(num_rules - 1):
            same_label = z3.And(
                rule_active[r], 
                rule_active[r+1], 
                rule_labels[r] == rule_labels[r+1]
            )
            constraints.append(
                z3.Implies(same_label, rule_lows_idx[r][0] <= rule_lows_idx[r+1][0])
            )

        # 3. Prevent perfectly identical active rules (anti-shadowing)
        for r1 in range(num_rules):
            for r2 in range(r1 + 1, num_rules):
                same_bounds = z3.And([
                    z3.And(rule_lows_idx[r1][p] == rule_lows_idx[r2][p],
                           rule_highs_idx[r1][p] == rule_highs_idx[r2][p])
                    for p in range(num_properties)
                ])
                constraints.append(
                    z3.Implies(z3.And(rule_active[r1], rule_active[r2]), z3.Not(same_bounds))
                )

        # At least one rule must be active overall
        constraints.append(z3.Or(*rule_active))
        
        # ----------------------------------------------------------------
        # Evaluate rules against every valid state
        # ----------------------------------------------------------------
        for i, variable in enumerate(policy_vars):
            values_dict  = variable_value_pairs[i]
            
            # Map float property values to precomputed integer indices
            prop_indices_concrete = []
            for p, pname in enumerate(property_names):
                val = values_dict[pname]
                idx = self.prop_sorted_vals[p].index(val)
                prop_indices_concrete.append(z3.IntVal(idx))

            chosen = self._apply_rules(
                prop_indices_concrete,
                rule_lows_idx,
                rule_highs_idx,
                rule_prop_active,
                rule_labels,
                num_rules,
                star_index,
                num_bits,
            )

            label_range = (
                args["family"].hole_to_option_labels[policy_indices[i]] + ["*"]
            )

            if label_range == labels:
                constraints.append(variable == chosen)
            else:
                label_indices = [label_to_index[l] for l in label_range]
                for index, label_index in enumerate(label_indices):
                    if self.args.relax:
                        if label_index != star_index:
                            constraints.append((variable == index) == (chosen == label_index))
                        else:
                            constraints.append(
                                (variable == index)
                                == z3.Or(chosen == label_index, chosen == star_index)
                            )
                    else:
                        constraints.append((variable == index) == (chosen == label_index))

        arguments = variables
        var_in_range_statement = variables_in_ranges(arguments)
        constraints += [function(*arguments), var_in_range_statement]

        # Add cause minimality: setting any variable that is fixed to "*" should imply that the constraint no longer holds
        # (This is HP minimality)
        # This has nothing to do with the rule list
        # for all i, if i is not "*", then the constraint with i set to "*" should not hold
        for i, variable in enumerate(policy_vars):
            label_range = (
                args["family"].hole_to_option_labels[policy_indices[i]] + ["*"]
            )
            copied_args = list(arguments)
            copied_args[i] = z3.BitVecVal(star_index, num_bits)
            constraints.append(
                z3.Implies(variable != star_index, z3.Not(function(*copied_args)))
            )

        return constraints

    def add_soft_constraints(self, solver):
        """
        Called after build_constraint() if the running solver is z3.Optimize.
        Adds penalties for active property flags to promote rule sparsity.
        """
        for expr, weight in self.soft_constraints:
            solver.add_soft(expr, weight=weight)

    # ------------------------------------------------------------------
    def show_result(self, model, _solver, **args):
        property_names = self.property_names
        num_rules      = self.args.rules
        num_bits       = max([x.size() for x in self.policy_vars])

        print("\n=== Rectangle Rule List ===")
        active_rules = []

        for r in range(num_rules):
            rule_active = model[z3.Bool(f"rule_{r}_active")]
            if not rule_active:
                continue

            label_idx  = model[z3.BitVec(f"rule_{r}_label", num_bits)].as_long()
            label_name = self.labels[label_idx]

            conditions = []
            for p, pname in enumerate(property_names):
                prop_active = model[z3.Bool(f"rule_{r}_prop_{p}_active")]
                if not prop_active:
                    continue

                lo_idx = model[z3.Int(f"rule_{r}_lo_idx_{p}")].as_long()
                hi_idx = model[z3.Int(f"rule_{r}_hi_idx_{p}")].as_long()

                lo_val = self.prop_sorted_vals[p][lo_idx]
                hi_val = self.prop_sorted_vals[p][hi_idx]

                conditions.append(f"{lo_val:.4f} <= {pname} <= {hi_val:.4f}")

            rule_str = "IF " + " AND ".join(conditions) + f"  THEN  {label_name}"
            active_rules.append(rule_str)
            print(f"  Rule {r}: {rule_str}")

        print("  DEFAULT: *")

        if self.args.pictures is not None:
            os.makedirs(self.args.pictures, exist_ok=True)
            with open(os.path.join(self.args.pictures, "rules.txt"), "w") as f:
                for line in active_rules:
                    f.write(line + "\n")
                f.write("DEFAULT: *\n")
