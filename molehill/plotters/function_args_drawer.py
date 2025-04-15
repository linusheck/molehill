import svgwrite

def draw_function_args(mole):
    function_args = mole.function_argument_tracker

    # Create an SVG matrix with text in each cell
    size_y = len(function_args)
    size_x = len(function_args[0]) if function_args else 0
    matrix = [["" for _ in range(size_x)] for _ in range(size_y)]
    for i in range(size_y):
        for j in range(size_x):
            matrix[i][j] = str(function_args[i][j])
    # Create a new SVG drawing
    dwg = svgwrite.Drawing("function_args.svg", profile="tiny")
    # Set the size of the SVG
    # Set a maximum size for the SVG
    max_size = 10000  # Maximum width or height in pixels
    width = size_x * 100
    height = size_y * 100
    if width > max_size or height > max_size:
        scale_factor = min(max_size / width, max_size / height)
        width = int(width * scale_factor)
        height = int(height * scale_factor)
    else:
        scale_factor = 1
    scale_mult = 100 * scale_factor
    dwg.viewbox(width=width, height=height)
    # Add the matrix to the SVG
    for i in range(size_y):
        for j in range(size_x):
            # Add a rectangle for each cell
            try:
                # Check if the value is a boolean
                if matrix[i][j] == "True":
                    fill_color = "limegreen"
                    matrix[i][j] = "True?"
                elif matrix[i][j] == "False":
                    fill_color = "tomato"
                    matrix[i][j] = "False?"
                else:
                    # Try to convert the text to a number
                    number = float(matrix[i][j])
                    # Map the number to a color (e.g., using a simple gradient)
                    if number == 0:
                        fill_color = "white"
                    else:
                        fill_color = f"rgb({max(0, int(255 - number * 15))}, {max(0, int(255 - number * 15))}, {min(255, int(200 + number * 20))})"
            except ValueError:
                # If it's not a number, use a shade of yellow based on the string hash
                hash_value = hash(matrix[i][j])
                fill_color = f"rgb(255, {220 + (hash_value % 36)}, {100 + (hash_value % 56)})"
            dwg.add(dwg.rect((j * scale_mult, i * scale_mult), (scale_mult, scale_mult), fill=fill_color))
            # Add text to each cell
            font_size = f"{scale_mult / 2}px" if len(matrix[i][j]) < 4 else f"{scale_mult / 5}px"
            dwg.add(dwg.text(matrix[i][j], insert=((j * scale_mult) + (scale_mult/2), (i * scale_mult) + (scale_mult/2)), text_anchor="middle", font_size=font_size))
    # Save the SVG to a file
    dwg.save()
