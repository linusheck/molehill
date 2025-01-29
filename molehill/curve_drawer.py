from PIL import Image, ImageFont, ImageDraw
import z3
from molehill.model_counters import ModelEnumeratingPlugin
import math
import matplotlib.pyplot as plt

# Function to map a 1D index to 2D Hilbert coordinates
def hilbert_index_to_xy(n, d):
    x, y = 0, 0
    s = 1
    while s < n:
        rx = 1 & (d // 2)
        ry = 1 & (d ^ rx)
        if ry == 0:
            if rx == 1:
                x, y = s - 1 - x, s - 1 - y
            x, y = y, x
        x += s * rx
        y += s * ry
        d //= 4
        s *= 2
    return x, y

def z_order_index_to_xy(n, d):
    x = 0
    y = 0
    for i in range(n):
        x |= ((d >> (2 * i)) & 1) << i
        y |= ((d >> (2 * i + 1)) & 1) << i
    return x, y

# Create a pixel-based image from the Hilbert curve
def add_pixels(pixels, size, red_numbers, color):
    # Map red numbers to pixels
    for num in red_numbers:
        x, y = z_order_index_to_xy(size, num)
        pixels[x, y] = color  # Red pixel

def draw_curve(num_bits, variables, s, p, model=None, gif=True):
    actual_bits = num_bits - 1
    size = math.ceil(math.sqrt(2**(actual_bits * len(variables))))
    print(size, size)
    image = Image.new("RGBA", (size, size), "black")
    pixels = image.load()
    new_assertions = p.model_counter.solver.assertions()[len(s.assertions()):]
    N = len(new_assertions)
    images = []
    possible_models = set([i for i in range(2**(actual_bits * len(variables)))])
    color = (245, 245, 220, 255)
    add_pixels(pixels, size, possible_models, color)
    font = ImageFont.truetype("Courier New Bold.ttf", 18)
    for j in range(0, N+1):
        print(f"Making image {j}/{N}")
        i = int(min(j * (float(len(new_assertions))/N), len(new_assertions)))
        s2 = z3.Solver()
        p2 = ModelEnumeratingPlugin(s2)
        p2.register_variables(variables)

        for a in s.assertions():
            s2.add(a)
        for a in new_assertions[:i+1]:
            s2.add(a)
        # get all models
        model_numbers = set()
        assert s2.check() == z3.unsat
        for m in p2.models:
            variable_values = sum([m[i][1].as_long() * 2**(i * actual_bits) for i in range(len(variables))])
            model_numbers.add(variable_values)
        assert model_numbers <= possible_models
        ruled_out_models = possible_models - model_numbers
        possible_models = model_numbers
        # make a table of four colors that fit (245, 245, 220, 255)
        high_contrast_colors = [
            (31, 119, 180, 255),  # Blue
            (255, 127, 14, 255),  # Orange
            (44, 160, 44, 255),   # Green
            (214, 39, 40, 255)    # Red
        ]
        reasons = [
            "DTMC reject",
            "DTMC counterexample",
            "MDP reject",
            "MDP counterexample"
        ]

        # color = plt.cm.ocean(float(i) / float(len(new_assertions)))
        color = (255, 0, 0, 255)
        if i < len(p.reasons):
            reason = p.reasons[i]
            for j, r in enumerate(reasons):
                if r in reason:
                    color = high_contrast_colors[j]
                    break

        # ints = tuple([int(255 * x) for x in color])
        add_pixels(pixels, size, ruled_out_models, color)
        if model is not None and j == N:
            model_tuples = [(var, model.eval(var)) for var in variables]
            x = sorted(model_tuples, key=lambda x: str(x[0]))
            model_number =  sum([x[i][1].as_long() * 2**(i * actual_bits) for i in range(len(variables))])
            # assert model_number in possible_models
            add_pixels(pixels, size, set([model_number]), (255, 0, 0, 255))
        if gif:
            copied_image = image.copy()
            copied_image = copied_image.resize((size * 10, size * 10), Image.Resampling.NEAREST)
            new_image = Image.new("RGBA", (size * 10, size * 20), "white")
            new_image.paste(copied_image, (0, 0))
            # write reason into image
            draw = ImageDraw.Draw(new_image)
            if i < len(p.reasons):
                draw.text((0, size * 10), p.reasons[i]+f"\n{len(possible_models)} models left\n"+str(new_assertions[i]), font=font, fill="black")
            elif model is not None:
                draw.text((0, size * 10), "model found:" + "\n".join([f"{var}={model.eval(var)}" for var in variables]), font=font, fill="black")
            images.append(new_image)
    if gif:
        images[0].save("image.gif", save_all=True, append_images=images[1:] + [images[-1].copy()] * 10, duration=100, loop=0)

    image = image.resize((size * 10, size * 10), Image.Resampling.NEAREST)
    image.save("image.png")
