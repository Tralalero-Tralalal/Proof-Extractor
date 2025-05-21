import re
import sys

def strip_proofs(src_path: str, dst_path: str):
    # Read source file
    with open(src_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Initialize match counters
    qed_count = 0
    defined_count = 0

    # Define a helper function to count matches while replacing
    def count_qed_match(match):
        nonlocal qed_count
        qed_count += 1
        return 'Proof. Admitted.'

    def count_defined_match(match):
        nonlocal defined_count
        defined_count += 1
        return 'Proof. Admitted.'

    # Remove everything between Proof and Qed (keeping Proof) and add Admitted
    stripped_qed = re.sub(r'Proof\.(.*?)Qed\.', count_qed_match, content, flags=re.DOTALL)

    # Remove everything between Proof and Defined (keeping Proof) and add Admitted
    stripped_defined = re.sub(r'Proof\.(.*?)Defined\.', count_defined_match, stripped_qed, flags=re.DOTALL)

    # Write to destination file
    with open(dst_path, 'w', encoding='utf-8') as f:
        f.write(stripped_defined)

    # Print the number of matches
    print(f"Found {qed_count} occurrences of Proof...Qed.")
    print(f"Found {defined_count} occurrences of Proof...Defined.")

# Command-line interface
if len(sys.argv) == 3:
    src = sys.argv[1]
    dst = sys.argv[2]
    strip_proofs(src, dst)
else:
    raise ValueError("Usage: python script.py <input_file.v> <output_file.v>")
