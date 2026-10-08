#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
imports=()
while IFS= read -r module; do
  [[ -z "$module" ]] || imports+=("$module")
done < mathlib-imports.txt
lake exe cache get "${imports[@]}"
