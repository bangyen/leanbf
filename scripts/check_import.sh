#!/bin/bash

# Check that each Lean directory has an aggregator module and that each aggregator
# imports all direct child modules. This guarantees full tree coverage while
# allowing hierarchical aggregation (folder-level import files).

set -euo pipefail

SEARCH_ROOTS=("LeanSharp" "Tests")
MATCHES=()

module_from_path() {
    local path="$1"
    echo "${path%.lean}" | tr '/' '.'
}

has_import() {
    local file="$1"
    local module="$2"
    awk -v module="$module" '
        $1 == "import" && $2 == module { found = 1 }
        END { exit(found ? 0 : 1) }
    ' "$file"
}

collect_dirs() {
    local root="$1"
    while IFS= read -r file; do
        local dir="${file%/*}"
        while [[ -n "$dir" ]]; do
            echo "$dir"
            if [[ "$dir" == "$root" ]]; then
                break
            fi
            dir="${dir%/*}"
        done
    done < <(git ls-files "$root" | awk '/\.lean$/') | sort -u
}

direct_child_lean_files() {
    local dir="$1"
    git ls-files "$dir" | awk -v prefix="$dir/" '
        $0 ~ /\.lean$/ && index($0, prefix) == 1 {
            remainder = substr($0, length(prefix) + 1)
            if (remainder !~ /\//) {
                print $0
            }
        }
    ' | sort
}

for root in "${SEARCH_ROOTS[@]}"; do
    while IFS= read -r dir; do
        [[ -z "$dir" ]] && continue

        aggregator="${dir}.lean"
        if [[ ! -f "$aggregator" ]]; then
            MATCHES+=("Missing aggregator file: ${aggregator}")
            continue
        fi

        while IFS= read -r child_file; do
            [[ -z "$child_file" ]] && continue
            [[ "$child_file" == "$aggregator" ]] && continue

            module="$(module_from_path "$child_file")"
            if ! has_import "$aggregator" "$module"; then
                MATCHES+=("${aggregator}: missing 'import ${module}'")
            fi
        done < <(direct_child_lean_files "$dir")
    done < <(collect_dirs "$root")
done

if [[ ${#MATCHES[@]} -gt 0 ]]; then
    echo "ERROR: Missing imports found in folder aggregators."
    printf "%s\n" "${MATCHES[@]}"
    exit 1
fi

echo "✓ All folder aggregators import their direct child modules."
exit 0