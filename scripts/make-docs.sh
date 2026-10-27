#!/usr/bin/env bash
# Generate the API documentation (doc-gen4).
#
# In this environment doc-gen4's dependency `UnicodeBasic` cannot resolve the
# external C symbol `unicode_case_lookup` when `precompileModules := true`, so
# loading each module's `.so` fails.  Disabling precompilation before the doc
# build works around it, and has to be reapplied after every `lake update`.
#
# Source links point at GitHub when DOCGEN_SRC=github and at local `file://`
# paths otherwise, which is the useful default when reading the docs locally.
# DOCGEN_EXTERNAL_BASE names the site that hosts the libraries this one builds
# on; see scripts/link-external-docs.py.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

UNICODE_LAKEFILE=".lake/packages/UnicodeBasic/lakefile.lean"
if [ -f "$UNICODE_LAKEFILE" ]; then
  sed -i 's/  precompileModules := true/  precompileModules := false/' "$UNICODE_LAKEFILE"
fi

lake build Cplib doc-gen4

DOC_DIR="$ROOT/.lake/build/doc"
DECL_DIR="$DOC_DIR/declarations"
rm -rf "$DOC_DIR"
mkdir -p "$DECL_DIR"

DOCGEN="$(lake env which doc-gen4)"
LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH
SOURCE_MODE="${DOCGEN_SRC:-file}"

# `lake build Cplib:docs` recursively generates documentation for every imported
# module.  Since the proof modules import Mathlib, that produces well over a
# thousand unrelated pages.  Invoke `single` only for `Cplib` modules.  The
# Lean search path is exported once above, avoiding a `lake env` startup for
# every module while retaining accurate per-file source links.
while IFS= read -r source; do
  module="${source%.lean}"
  module="${module//\//.}"
  if [ "$SOURCE_MODE" = github ]; then
    source_uri="https://github.com/KowerKoint/cplib-lean/blob/main/$source"
  else
    source_uri="file://$ROOT/$source"
  fi
  "$DOCGEN" single --build "$ROOT/.lake/build" "$module" "$source_uri"
done < <(find Cplib -type f -name '*.lean' -print | LC_ALL=C sort; printf '%s\n' Cplib.lean)

"$DOCGEN" index --build "$ROOT/.lake/build"

# Those skipped modules are still linked to from the generated pages, so send
# every link that has no page here to a site that does host one.
python3 "$ROOT/scripts/link-external-docs.py" "$DOC_DIR" \
  --cache "$ROOT/.lake/build/declaration-data-external.bmp" \
  ${DOCGEN_EXTERNAL_BASE:+--base-url "$DOCGEN_EXTERNAL_BASE"}

echo
echo "Generated the documentation at $ROOT/.lake/build/doc/index.html"
echo "  for instance: xdg-open $ROOT/.lake/build/doc/Cplib.html"
