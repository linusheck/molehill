import sys
import pathlib
import tabulate
from functools import partial
from tabulate import Line, _latex_line_begin_tabular, _latex_row

if len(sys.argv) != 2:
    print("Usage: python tree-log.py <folder>")
    sys.exit(1)
folder = sys.argv[1]

table_tree = []
table_no_tree = []


# Find last line: --nodes x
def last_nodes(lines):
    for line in reversed(lines):
        if line.startswith("Running with --nodes "):
            return line.split()[3]
    return "?"

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
    if not file.name.startswith("SMPMC"):
        continue
    name = file.name.replace("SMPMC.benchmark-general-sat_mem_1_", "").replace(".yml.log", "")
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        family_size_here = family_size(lines)
        print(family_size_here)
        quotient_size_here = quotient_size(lines)
        if "sat\n" in lines:
            last_nodes_line = last_nodes(lines)
            table_tree.append([name, last_nodes_line, family_size_here, quotient_size_here])
        else:
            last_nodes_line = last_nodes(lines)
            if last_nodes_line == "?" or last_nodes_line == "1":
                table_no_tree.append([name, last_nodes_line, family_size_here, quotient_size_here])
            else:
                table_no_tree.append([name, int(last_nodes_line) - 2, family_size_here, quotient_size_here])


# lineabove=_latex_line_begin_tabular,
# linebelowheader=Line("\\hline", "", "", ""),
# linebetweenrows=None,
# linebelow=Line("\\hline\n\\end{tabular}", "", "", ""),
# headerrow=partial(_latex_row, escrules={}),
# datarow=partial(_latex_row, escrules={}),
# padding=1,
# with_header_hide=None,


tabulate._table_formats["latex_booktabs_raw"] = tabulate.TableFormat(
    lineabove=partial(_latex_line_begin_tabular, booktabs=True),
    linebelowheader=Line("\\midrule", "", "", ""),
    linebetweenrows=None,
    linebelow=Line("\\bottomrule\n\\end{tabular}", "", "", ""),
    headerrow=partial(_latex_row, escrules={}),
    datarow=partial(_latex_row, escrules={}),
    padding=1,
    with_header_hide=None,
)

# Print the tables in LaTeX format using booktabs
print("With Tree (LaTeX):")
print(tabulate.tabulate(table_tree, headers=["File", "Number of Nodes", "Family Size", "Size of \C(\mathbb{V})"], tablefmt="latex_booktabs_raw"))
print("\nWithout Tree (LaTeX):")
print(tabulate.tabulate(table_no_tree, headers=["File", "No Tree with $\leq$ Nodes", "Family Size", "Size of \C(\mathbb{V})"], tablefmt="latex_booktabs_raw"))
