#!/bin/sh
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
BIN="$SCRIPT_DIR/_build/default/bin/main.exe"

if [ "${ANVIL_SKIP_BUILD:-0}" != "1" ]; then
  (cd "$SCRIPT_DIR" && dune build ./bin/main.exe >/dev/null)
fi

exec "$BIN" "$@"
