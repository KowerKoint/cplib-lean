#!/usr/bin/env bash
# Report the module a declaration comes from, in the toolchain this package
# pins rather than in the published documentation for Mathlib master.
#
#   scripts/whereis.sh Nat.isPowerOfTwo Finset.sum_comm
#   scripts/whereis.sh -s nextPowerOfTwo      # substring of a name
#
# Each run loads all of Mathlib, which costs about ten seconds.  To ask many
# questions, open scripts/WhereIs.lean in an editor instead and write the
# `#whereis` lines there; the language server keeps the imports loaded.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

search=no
if [ "${1:-}" = "-s" ] || [ "${1:-}" = "--search" ]; then
  search=yes
  shift
fi

if [ "$#" -eq 0 ]; then
  echo "usage: scripts/whereis.sh [-s] NAME..." >&2
  exit 2
fi

query="$(mktemp "${TMPDIR:-/tmp}/whereis-XXXXXX.lean")"
trap 'rm -f "$query"' EXIT

# `#whereis` itself lives in scripts/WhereIs.lean, so the queries are simply
# appended to a copy of it.
cp scripts/WhereIs.lean "$query"
for name in "$@"; do
  if [ "$search" = yes ]; then
    printf '#whereis "%s"\n' "$name" >> "$query"
  else
    printf '#whereis %s\n' "$name" >> "$query"
  fi
done

# Strip the temporary file's location from the messages, which says nothing
# useful about a query.
lake env lean "$query" 2>&1 | sed -E "s|^${query}:[0-9]+:[0-9]+: ||"
