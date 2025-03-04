import os

# def command(P1,P2,P3,P4):
#     return f"../../../storm/build_release/bin/storm --prism safety.prism -prop sketch.props -const \"P1={P1},P2={P2},P3={P3},P4={P4}\" --exportbuild dots/sketch{P1}{P2}{P3}{P4}.dot -bisim"
# for P1 in range(4):
#     for P2 in range(4):
#         for P3 in range(4):
#             for P4 in range(4):
#                 c = command(P1,P2,P3,P4)
#                 print(c)
#                 os.system(c)
#                 os.system(f"python change_dot.py dots/sketch{P1}{P2}{P3}{P4}.dot > dots_simple/sketch{P1}{P2}{P3}{P4}.dot")
#                 os.system(f"dot -Tsvg -Gsize=15,15\\! -odots_svgs/sketch{P1}{P2}{P3}{P4}.svg dots_simple/sketch{P1}{P2}{P3}{P4}.dot")

# put svgs into grid in a new svg

# create a new svg
svg = open("dots_svgs/sketch.svg", "w")
svg.write("""<svg xmlns="http://www.w3.org/2000/svg" width="100%" height="100%" viewBox="0 0 100 100" preserveAspectRatio="xMidYMid meet">
""")
for P1 in range(4):
    for P2 in range(4):
        for P3 in range(4):
            for P4 in range(4):
                svg.write(f"""<g>
                {open(f"dots_svgs/sketch{P1}{P2}{P3}{P4}.svg").read()}
</g>
""")
svg.write("</svg>")
svg.close()