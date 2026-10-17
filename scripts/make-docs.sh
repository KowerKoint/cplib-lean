#!/usr/bin/env bash
# ローカルで API ドキュメントを生成する (doc-gen4)。
#
# この環境では doc-gen4 の依存 `UnicodeBasic` が `precompileModules := true` の場合に
# 外部 C シンボル (unicode_case_lookup) を解決できず、各モジュールの .so 読み込みに失敗する。
# そのため doc ビルド前に precompileModules を無効化する (lake update で戻るため都度適用)。
#
# また、git リモートを前提とする GitHub ソースリンクの代わりに、ローカルの file:// リンクを使う
# (DOCGEN_SRC=file)。GitHub Pages 等で公開する際は DOCGEN_SRC=github と git remote 設定に切り替える。
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

echo
echo "ドキュメントを生成しました: $ROOT/.lake/build/doc/index.html"
echo "  例: xdg-open $ROOT/.lake/build/doc/Cplib.html"
