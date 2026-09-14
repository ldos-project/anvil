#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
examples_root="$repo_root/vulcan_examples"
anvil_bin="$repo_root/anvil"

usage() {
  cat <<'EOF'
Usage: scripts/run_strict_vulcan_examples.sh [--keep-logs] [PATH ...]

Runs `anvil --strict --verify` on the vulcan example files.
By default, support templates such as `basic/template.cpp` are skipped.

Arguments:
  PATH           Optional example file or directory. If omitted, all source
                 files under `vulcan_examples/` are checked.

Options:
  --keep-logs    Preserve per-file stdout/stderr logs and print the log dir.
  -h, --help     Show this help text.

Environment:
  ANVIL_SKIP_BUILD=1   Skip the initial `dune build ./bin/main.exe`.
EOF
}

keep_logs=0
inputs=()

while [ "$#" -gt 0 ]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --keep-logs)
      keep_logs=1
      shift
      ;;
    *)
      inputs+=("$1")
      shift
      ;;
  esac
done

if [ ! -x "$anvil_bin" ]; then
  echo "missing executable wrapper: $anvil_bin" >&2
  exit 2
fi

if [ "${ANVIL_SKIP_BUILD:-0}" != "1" ]; then
  (
    cd "$repo_root"
    dune build ./bin/main.exe >/dev/null
  )
fi

files=()

add_file() {
  local path="$1"

  case "$path" in
    */template.cpp)
      return
      ;;
  esac

  case "$path" in
    *.c|*.cc|*.cpp|*.cxx)
      files+=("$path")
      ;;
  esac
}

collect_from_path() {
  local raw="$1"
  local path="$raw"

  if [ ! -e "$path" ]; then
    path="$repo_root/$raw"
  fi

  if [ ! -e "$path" ]; then
    echo "path not found: $raw" >&2
    exit 2
  fi

  if [ -d "$path" ]; then
    while IFS= read -r file; do
      add_file "$file"
    done < <(find "$path" -type f \( -name '*.c' -o -name '*.cc' -o -name '*.cpp' -o -name '*.cxx' \) | sort)
  else
    add_file "$path"
  fi
}

if [ "${#inputs[@]}" -eq 0 ]; then
  collect_from_path "$examples_root"
else
  for input in "${inputs[@]}"; do
    collect_from_path "$input"
  done
fi

if [ "${#files[@]}" -eq 0 ]; then
  echo "no vulcan example source files found" >&2
  exit 2
fi

deduped_files=()
while IFS= read -r file; do
  deduped_files+=("$file")
done < <(printf '%s\n' "${files[@]}" | awk '!seen[$0]++')
files=("${deduped_files[@]}")

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/anvil-vulcan-strict.XXXXXX")
logs_announced=0

cleanup() {
  if [ "$keep_logs" = "1" ]; then
    if [ "$logs_announced" = "0" ]; then
      echo "Logs kept in $tmpdir"
    fi
  else
    rm -rf "$tmpdir"
  fi
}

trap cleanup EXIT

total=0
passed=0
failures=()

for file in "${files[@]}"; do
  total=$((total + 1))
  rel="$file"
  case "$rel" in
    "$repo_root"/*)
      rel="${rel#"$repo_root"/}"
      ;;
  esac

  safe_name=$(printf '%s' "$rel" | tr '/ ' '__')
  stdout_path="$tmpdir/$safe_name.stdout"
  stderr_path="$tmpdir/$safe_name.stderr"

  if ANVIL_SKIP_BUILD=1 "$anvil_bin" --strict --verify "$file" >"$stdout_path" 2>"$stderr_path"; then
    passed=$((passed + 1))
    printf 'PASS  %s\n' "$rel"
  else
    summary=$(sed -n '1p' "$stderr_path")
    if [ -z "$summary" ]; then
      summary=$(sed -n '1p' "$stdout_path")
    fi
    if [ -z "$summary" ]; then
      summary="<no output>"
    else
      summary=$(printf '%s\n' "$summary" | sed "s|$repo_root/||g")
    fi
    failures+=("$rel :: $summary")
    printf 'FAIL  %s\n' "$rel"
  fi
done

echo "Passed $passed/$total vulcan examples."

if [ "${#failures[@]}" -gt 0 ]; then
  echo "Failures:"
  for failure in "${failures[@]}"; do
    echo "  $failure"
  done
  if [ "$keep_logs" = "0" ]; then
    keep_logs=1
    logs_announced=1
    echo "Logs kept in $tmpdir"
  fi
  exit 1
fi
