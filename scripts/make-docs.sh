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

DOCGEN_SRC="${DOCGEN_SRC:-file}" lake build Cplib:docs

echo
echo "ドキュメントを生成しました: $ROOT/.lake/build/doc/index.html"
echo "  例: xdg-open $ROOT/.lake/build/doc/Cplib.html"
