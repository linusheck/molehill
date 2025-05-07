import argparse
import os

argument_parser = argparse.ArgumentParser(description="Create a new benchmark")
argument_parser.add_argument("category", type=str, help="Category of the benchmark")
argument_parser.add_argument("input_file", type=str, help="Path to the input file")
argument_parser.add_argument(
    "property_file", type=str, help="Path to the property file"
)
argument_parser.add_argument(
    "expected_verdict", type=str, help="Expected verdict of the property"
)
argument_parser.add_argument(
    "--iterate-memory",
    action="store_true",
    help="Flag to indicate whether to iterate memory",
)

args = argument_parser.parse_args()
input_file = args.input_file
property_file = args.property_file
expected_verdict = args.expected_verdict

template = f"""
format_version: "2.0"

input_files:
- {{input_file}}

properties:
  - property_file: {{property_file}}
    expected_verdict: {{expected_verdict}}
"""


def write(name, template):
    category = args.category
    if not os.path.exists(f"files/{category}"):
        os.makedirs(f"files/{category}")
    with open(f"files/{category}/{name}.yml", "w") as f:
        f.write(
            template.format(
                input_file=input_file,
                property_file=property_file,
                expected_verdict=expected_verdict,
            )
        )

if not args.iterate_memory:
    write(input_file.split("/")[-1].split(".")[0], template)
else:
    for i in range(1, 5):
        new_template = template + f"""
options:
    memory: {i}
"""
        write(f"{input_file.split('/')[-1].split('.')[0]}_{i}", new_template)
