import os
import re

# def command(P1,P2):
#     return f"../../../storm/build_release/bin/storm --prism safety.prism -prop sketch.props -const \"P1={P1},P2={P2}\" --exportbuild dots/sketch{P1}{P2}.dot"
# for P1 in range(4):
#     for P2 in range(4):
#         c = command(P1,P2)
#         print(c)
#         os.system(c)
#         os.system(f"python change_dot.py dots/sketch{P1}{P2}.dot > dots_simple/sketch{P1}{P2}.dot")
#         os.system(f"dot -Tsvg -Gsize=12,12\\! -odots_svgs/sketch{P1}{P2}.svg dots_simple/sketch{P1}{P2}.dot")

# put svgs into grid in a new svg

CELL_SIZE = 1000
# create a new svg
svg = open("dots_svgs/sketch.svg", "w")
svg.write(
    f"""<svg xmlns="http://www.w3.org/2000/svg" width="100%" height="100%" viewBox="0 0 {CELL_SIZE * 4} {CELL_SIZE * 4}" preserveAspectRatio="xMidYMid meet">
"""
)
for P1 in range(4):
    for P2 in range(4):
        # Calculate x, y position for each SVG in the grid
        x = P2 * CELL_SIZE
        y = P1 * CELL_SIZE
        # Read the SVG content and remove the outer <svg> tags
        with open(f"dots_svgs/sketch{P1}{P2}.svg", encoding="utf-8") as f:
            svg_content = f.read()
        svg_tag_line = svg_content.split("\n")[6]
        match = re.search(r'width="([\d.]+)pt"\s+height="([\d.]+)pt"', svg_tag_line)
        if match:
            width_pt = float(match.group(1))
            height_pt = float(match.group(2))
            print(f"SVG {P1},{P2} width: {width_pt}pt, height: {height_pt}pt")
        else:
            print(f"Could not extract width/height for SVG {P1},{P2}")
        print(width_pt, height_pt)
        svg_content = "\n".join(svg_content.split("\n")[7:][:-2])

        # Remove the outer <svg> tags
        svg_inner = svg_content
        # if "<svg" in svg_content:
        #     svg_inner = svg_content.split(">", 1)[1].rsplit("</svg>", 1)[0]
        svg.write(
            f"""<g transform="translate({x + width_pt/2},{y +height_pt/2})">
    {svg_inner}
    </g>
    """
        )
svg.write("</svg>")
svg.close()
