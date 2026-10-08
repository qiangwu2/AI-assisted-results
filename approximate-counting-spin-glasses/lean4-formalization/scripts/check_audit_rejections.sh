#!/usr/bin/env bash
set -euo pipefail
# Run after verify.sh has compiled the aggregate import.
fixture_dir="$(mktemp -d "$PWD/.lake/audit-fixtures.XXXXXX")"
trap 'rm -rf "$fixture_dir"' EXIT
awk 'BEGIN { copying=0 } /^open Lean Elab Command in/ { copying=1 } copying { print }' \
  Audit.lean > "$fixture_dir/body.txt"
for kind in custom_axiom public_placeholder private_placeholder; do
  fixture="$fixture_dir/$kind.lean"
  cat > "$fixture" <<'LEAN'
import SpinGlass
import Lean.Util.CollectAxioms
LEAN
  case "$kind" in
    custom_axiom)
      echo 'axiom SpinGlass.auditFixture : False' >> "$fixture" ;;
    public_placeholder)
      echo 'theorem SpinGlass.auditFixture : True := by sorry' >> "$fixture" ;;
    private_placeholder)
      cat >> "$fixture" <<'LEAN'
namespace SpinGlass
private theorem auditFixture : True := by sorry
end SpinGlass
LEAN
      ;;
  esac
  cat "$fixture_dir/body.txt" >> "$fixture"
  if lean "$fixture" > "$fixture_dir/result.log" 2>&1; then
    echo "FAIL: the $kind fixture was accepted" >&2
    exit 1
  fi
  if ! grep -q 'Disallowed axiom' "$fixture_dir/result.log"; then
    cat "$fixture_dir/result.log" >&2
    echo "FAIL: the $kind fixture failed for an unexpected reason" >&2
    exit 1
  fi
  echo "PASS: $kind was rejected by the axiom audit"
  grep 'Disallowed axiom' "$fixture_dir/result.log"
done
