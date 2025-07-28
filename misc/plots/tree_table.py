import sys
import pathlib
import tabulate
from functools import partial
from tabulate import Line, _latex_line_begin_tabular, _latex_row

if len(sys.argv) != 3:
    print("Usage: python tree-log.py <folder>")
    sys.exit(1)
folder = sys.argv[1]
method = sys.argv[2]

tree_table = {}


def nodes(lines):
    for line in lines:
        if "--nodes" in line:
            nodes_index = line.index("--nodes") + len("--nodes") + 1
            next_space = line.find(" ", nodes_index)
            return int(line[nodes_index:next_space].strip())

def family_size(lines):
    # e.g. Family size 7.23e+2821
    for line in lines:
        if line.startswith("Family size "):
            # convert to latex
            return "$" + line.split()[2].replace("e+", "\\cdot 10^{") + "}" + "$"

def quotient_size(lines):
    # e.g. Quotient size 21233
    for line in lines:
        if line.startswith("Quotient size "):
            return line.split()[2]

for file in pathlib.Path(folder).glob("*.log"):
    print(file)
    if not file.name.startswith(method):
        continue
    name = file.name.replace(method + ".benchmark-general-sat_", "").replace(".yml.log", "")
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        family_size_here = family_size(lines)
        quotient_size_here = quotient_size(lines)
        tree_sat = "sat\n" in lines
        tree_unsat = "unsat\n" in lines
        num_nodes = nodes(lines)
        print(f"Processing {name}: Family Size: {family_size_here}, Quotient Size: {quotient_size_here}, Nodes: {nodes}, Tree SAT: {tree_sat}, Tree UNSAT: {tree_unsat}")
        if tree_sat:
            if name not in tree_table:
                tree_table[name] = {}
            tree_table[name][nodes] = {
                "family_size": family_size_here,
                "quotient_size": quotient_size_here,
                "sat": True
            }
        #     tree_table[name][]
        # if "sat\n" in lines:
        #     table_tree.append([name, last_nodes_line, family_size_here, quotient_size_here])
        # else:
        #     last_nodes_line = last_nodes(lines)
        #     if last_nodes_line == "?" or last_nodes_line == "1":
        #         table_no_tree.append([name, last_nodes_line, family_size_here, quotient_size_here])
        #     else:
        #         table_no_tree.append([name, int(last_nodes_line) - 2, family_size_here, quotient_size_here])


# # lineabove=_latex_line_begin_tabular,
# # linebelowheader=Line("\\hline", "", "", ""),
# # linebetweenrows=None,
# # linebelow=Line("\\hline\n\\end{tabular}", "", "", ""),
# # headerrow=partial(_latex_row, escrules={}),
# # datarow=partial(_latex_row, escrules={}),
# # padding=1,
# # with_header_hide=None,

# # sort the tables by the first column
# table_tree.sort(key=lambda x: x[0])
# table_no_tree.sort(key=lambda x: x[0])

# tabulate._table_formats["latex_booktabs_raw"] = tabulate.TableFormat(
#     lineabove=partial(_latex_line_begin_tabular, booktabs=True),
#     linebelowheader=Line("\\midrule", "", "", ""),
#     linebetweenrows=None,
#     linebelow=Line("\\bottomrule\n\\end{tabular}", "", "", ""),
#     headerrow=partial(_latex_row, escrules={}),
#     datarow=partial(_latex_row, escrules={}),
#     padding=1,
#     with_header_hide=None,
# )

# # Print the tables in LaTeX format using booktabs
# print("With Tree (LaTeX):")
# print(tabulate.tabulate(table_tree, headers=["File", "Number of Nodes", "Family Size", "Size of \C(\mathbb{V})"], tablefmt="latex_booktabs_raw"))
# print("\nWithout Tree (LaTeX):")
# print(tabulate.tabulate(table_no_tree, headers=["File", "No Tree with $\leq$ Nodes", "Family Size", "Size of \C(\mathbb{V})"], tablefmt="latex_booktabs_raw"))
