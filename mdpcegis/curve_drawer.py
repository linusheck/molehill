from PIL import Image

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

def new_image(size):
    return Image.new("RGBA", (size, size), "black")

# Create a pixel-based image from the Hilbert curve
def add_pixels(pixels, size, red_numbers, color):
    # Map red numbers to pixels
    for num in red_numbers:
        x, y = z_order_index_to_xy(size, num)
        pixels[x, y] = color  # Red pixel

# Example usage
if __name__ == "__main__":
    m = 6  # Number of bits
    order = m // 2
    red_numbers = [5, 17, 42]  # Replace with your n m-bit numbers
    image = create_hilbert_image(order, red_numbers)
    image.show()  # Display the image
