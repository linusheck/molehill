import sys

input_file = sys.argv[1]
content = open(input_file).read()

lines = content.split("\n")
output_lines = []

for l in lines:
    if not "[" in l:
        output_lines.append(l)
        continue
    beginning = l.split("[")
    if "->" in beginning:
        output_lines.append(beginning[0] + "[arrowhead=none,label=\"\"];")
    else:
        output_lines.append(beginning[0] + "[shape=point,label=\"\"];")
    

print("\n".join(output_lines))
