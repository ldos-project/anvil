#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
cases_dir="$script_dir/e2e_cases"
anvil_bin="$repo_root/anvil"

if ! command -v gcc >/dev/null 2>&1; then
  echo "gcc not found in PATH" >&2
  exit 2
fi

if [ "${ANVIL_SKIP_BUILD:-0}" != "1" ]; then
  (
    cd "$repo_root"
    dune build ./bin/main.exe >/dev/null
  )
fi

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/anvil-e2e.XXXXXX")
trap 'rm -rf "$tmpdir"' EXIT

total=0
passed=0
failures=()

for file in "$cases_dir"/*.c; do
  [ -e "$file" ] || continue

  total=$((total + 1))
  name=$(basename "$file")
  include_dir=$(dirname "$file")
  expected=$(sed -En '1s@/\* EXPECT: (PASS|FAIL) \*/@\1@p' "$file")

  if [ -z "$expected" ]; then
    failures+=("$name (missing EXPECT comment)")
    continue
  fi

  if ! gcc -std=c11 -Wall -Wextra -Werror -I"$include_dir" -c "$file" -o "$tmpdir/$name.o" \
    >"$tmpdir/$name.gcc.stdout" 2>"$tmpdir/$name.gcc.stderr"; then
    failures+=("$name (gcc rejected the original program)")
    continue
  fi

  actual="FAIL"
  if ANVIL_SKIP_BUILD=1 "$anvil_bin" "$file" \
    >"$tmpdir/$name.anvil.c" 2>"$tmpdir/$name.anvil.stderr"; then
    if gcc -std=c11 -Wall -Wextra -Werror -I"$include_dir" -c "$tmpdir/$name.anvil.c" \
      -o "$tmpdir/$name.anvil.o" \
      >"$tmpdir/$name.anvil-gcc.stdout" 2>"$tmpdir/$name.anvil-gcc.stderr"; then
      actual="PASS"
    fi
  fi

  if [ "$actual" = "$expected" ]; then
    passed=$((passed + 1))
  else
    failures+=("$name (expected $expected, got $actual)")
  fi
done

echo "Passed $passed/$total tests."

if [ "${#failures[@]}" -gt 0 ]; then
  echo "Failing tests:"
  for failure in "${failures[@]}"; do
    echo "  $failure"
  done
  exit 1
fi
