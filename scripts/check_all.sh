#!/bin/bash

# Run all quality guard scripts in a consistent order.
# Stops on the first failure and returns a non-zero exit code.

set -euo pipefail

# Keep format check last so style fixes do not hide earlier semantic failures.
SCRIPTS=(
    "scripts/check_banned.sh"
    "scripts/check_import.sh"
    "scripts/check_simp.sh"
    "scripts/check_copyright.sh"
    "scripts/check_description.sh"
    "scripts/check_long_file.sh"
    "scripts/check_proof_length.sh"
    "scripts/check_naming.sh"
    "scripts/format_lean.sh --check"
)

for entry in "${SCRIPTS[@]}"; do
    echo "==> Running: ${entry}"
    eval "${entry}"
done

echo "✓ All guard checks passed."
