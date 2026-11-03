#!/usr/bin/env bash
# Exercises `anvil --gate`, the evolve-block safety gate that Vulcan runs on
# every LLM-generated candidate. Mirrors run_e2e.sh: each case in gate_cases/
# declares its expected verdict on the first line as
#
#   // GATE: SAFE      -- the gate must accept it
#   // GATE: UNSAFE    -- the gate must reject it (exit non-zero)
#
# Cases are evolve blocks (listener config + scoring function), not whole
# programs, so they are fed to the gate on stdin and never compiled by gcc.
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
cases_dir="$script_dir/gate_cases"
anvil_bin="$repo_root/anvil"

if [ "${ANVIL_SKIP_BUILD:-0}" != "1" ]; then
  (cd "$repo_root" && dune build ./bin/main.exe >/dev/null)
fi

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/anvil-gate.XXXXXX")
trap 'rm -rf "$tmpdir"' EXIT

total=0
passed=0
failures=()

for file in "$cases_dir"/*.cpp; do
  [ -e "$file" ] || continue

  total=$((total + 1))
  name=$(basename "$file")
  expected=$(sed -En '1s@// GATE: (SAFE|UNSAFE)@\1@p' "$file")

  if [ -z "$expected" ]; then
    failures+=("$name (missing '// GATE: SAFE|UNSAFE' first line)")
    continue
  fi

  actual="UNSAFE"
  if ANVIL_SKIP_BUILD=1 "$anvil_bin" --gate <"$file" \
    >"$tmpdir/$name.stdout" 2>"$tmpdir/$name.stderr"; then
    actual="SAFE"
  fi

  if [ "$actual" = "$expected" ]; then
    passed=$((passed + 1))
  else
    detail=$(head -1 "$tmpdir/$name.stderr" 2>/dev/null || true)
    failures+=("$name (expected $expected, got $actual) ${detail}")
  fi
done

echo "Passed $passed/$total gate tests."

if [ "${#failures[@]}" -gt 0 ]; then
  echo "Failing tests:"
  for failure in "${failures[@]}"; do
    echo "  $failure"
  done
  exit 1
fi
