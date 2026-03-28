#!/bin/bash

# Check that Lean module docs follow a consistent structure.
# We require a '/-! ... -/' block with a title, and conditional non-empty sections:
# - require a Definitions section if the file defines defs/abbrevs/classes/structures/instances
# - require a Theorems section if the file contains theorem/lemma declarations

MATCHES=()

section_has_content() {
    local module_doc="$1"
    local section_kind="$2"

    awk -v section_kind="$section_kind" '
        BEGIN { in_section = 0; has_content = 0 }
        {
          line = tolower($0)
        }
        section_kind == "definitions" && line ~ /^[[:space:]]*##[[:space:]]+.*definitions?([^a-z0-9_]|$)/ { in_section = 1; next }
        section_kind == "theorems" && line ~ /^[[:space:]]*##[[:space:]]+.*theorems?([^a-z0-9_]|$)/ { in_section = 1; next }
        in_section && $0 ~ /^[[:space:]]*##[[:space:]]+/ { exit(has_content ? 0 : 1) }
        in_section && $0 ~ /[^[:space:]]/ { has_content = 1 }
        END { if (in_section == 0) exit 2; exit(has_content ? 0 : 1) }
    ' <<< "$module_doc"
}

while IFS= read -r file_path; do
    [ -z "$file_path" ] && continue

    module_doc="$(awk '
        BEGIN { in_doc = 0; found = 0 }
        /^[[:space:]]*\/-!/ && found == 0 { in_doc = 1; found = 1 }
        in_doc { print }
        in_doc && /-\/[[:space:]]*$/ { exit }
    ' "$file_path")"

    if [ -z "$module_doc" ]; then
        MATCHES+=("$file_path: missing module doc block (/-! ... -/)")
        continue
    fi

    if ! printf "%s\n" "$module_doc" | grep -qE '^[[:space:]]*#[[:space:]]+\S'; then
        MATCHES+=("$file_path: missing module title heading (# ...)")
    fi

    has_defs=0
    if grep -qE '^[[:space:]]*(noncomputable[[:space:]]+)?(def|abbrev|class|structure|instance)\b' "$file_path"; then
        has_defs=1
    fi

    has_theorems=0
    if grep -qE '^[[:space:]]*(protected[[:space:]]+)?(theorem|lemma)\b' "$file_path"; then
        has_theorems=1
    fi

    if [ "$has_defs" -eq 1 ] && ! printf "%s\n" "$module_doc" | grep -qiE '^[[:space:]]*##[[:space:]]+.*definitions?\b'; then
        MATCHES+=("$file_path: missing Definitions section heading (## ... Definitions ...)")
    elif [ "$has_defs" -eq 1 ]; then
        if ! section_has_content "$module_doc" "definitions"; then
            MATCHES+=("$file_path: Definitions section is empty")
        fi
    fi

    if [ "$has_theorems" -eq 1 ] && ! printf "%s\n" "$module_doc" | grep -qiE '^[[:space:]]*##[[:space:]]+.*theorems?\b'; then
        MATCHES+=("$file_path: missing Theorems section heading (## ... Theorems ...)")
    elif [ "$has_theorems" -eq 1 ]; then
        if ! section_has_content "$module_doc" "theorems"; then
            MATCHES+=("$file_path: Theorems section is empty")
        fi
    fi
done < <(git ls-files '*.lean')

if [ "${#MATCHES[@]}" -gt 0 ]; then
    echo "ERROR: Module documentation structure check failed."
    echo "Each Lean file needs a module doc title, plus required non-empty Definitions/Theorems sections."
    printf "%s\n" "${MATCHES[@]}"
    exit 1
fi

echo "✓ All Lean files satisfy module documentation structure rules."
exit 0
