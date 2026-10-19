# Cplib

競技プログラミング (AtCoder 等) 向けのアルゴリズム / データ構造ライブラリ。
実装に加えて、可能なものは Lean 4 で正しさの定理証明を与えることを目指す。

- **Lean**: `v4.22.0` (AtCoder と同一)
- **Mathlib**: `v4.22.0`
- **ドキュメント**: [doc-gen4](https://github.com/leanprover/doc-gen4) (`v4.22.0`)

## 方針

- AtCoder のコンテストに参加するために必要な、実用上十分な範囲を網羅することを目指す。
- 趣味のライブラリとして、実行時性能だけでなく、実装の美しさ、Lean らしさ、証明のしやすさも
  重視する。一方で、構造上の美しさのために性能を大きく損なう設計は採用しない。例えばヒープや
  セグメント木は、帰納型による明示的な木ではなく配列を使って実装し、配列上の実装と抽象的な性質の
  隔たりは `Lemmas` の定理で補う。
- 学術用途の形式化ライブラリではなく、定理を外部 API として活用することも主目的にはしない。
  証明は、実装が期待どおりに動くことを静的に確認するテストとして、主要な操作と性質を網羅するために
  用いる。そのため、意味論上中心となる API は証明する一方、それから直接導かれる些末な利便 API は
  未証明でもよい。例えば `Cplib.SegTree.get` の性質は証明しても、`get!` や `get?` について同様の定理を
  個別には用意しないことがある。

## 構成

アルゴリズム、グラフ、データ構造、汎用ユーティリティなどの分類ごとに、`Cplib` 以下へ
モジュールを配置する。`Std` / `Batteries` の慣習に倣い、実装と定理は原則として次のように分割する
(`Std.Data.HashMap.{Basic,Lemmas}` と同じ):

- `Cplib.<分類>.<名前>.Basic` … 実装。他の `Basic` のみに依存し、**`Mathlib` を import しない**。
- `Cplib.<分類>.<名前>.Lemmas` … 定理。`Basic` と証明用の依存 (`Mathlib` 等) を import する。
- `Cplib.<分類>.<名前>` … 上記をまとめて読み込む集約モジュール。`Cplib.lean` はこれを import する。

ライブラリ固有の公開 API は `Cplib` 名前空間に置く。ただし、`Nat.midpoint`、
`Array.lowerBound` のように既存型の拡張として定義する API は、その型の名前空間に置く。

**実装だけを軽く使いたい場合 (AtCoder 提出など) は `...Basic` を直接 import する。**
`Lemmas` (および `Mathlib`) を引かないのでビルドが速い。実装を編集したときの再ビルドも、
`Basic` が `Mathlib` 非依存なので軽い。

## ビルド

```sh
# 依存解決 (初回・依存更新時)
lake update

# Mathlib のビルド済みキャッシュを取得 (初回ビルドを高速化)
lake exe cache get

# ライブラリ全体のビルド
lake build
```

## AtCoder 用の単一ファイル生成

`scripts/bundle.py` はエントリファイルから到達可能な `Cplib.*` import を依存順に
展開する。AtCoder 側に存在する Mathlib / Std などの import は先頭に残す。生成物には、
AtCoder の生成 AI 利用ルールに基づく参照 URL と MIT ライセンス全文をコメントとして付加する。

```sh
python3 scripts/bundle.py path/to/Main.lean -o Submit.lean
```

参照 URL は `--source-url`、ライセンスファイルは `--license` で差し替えられる。
ライセンスを埋め込まない場合は `--no-license` を指定する。

生成後のファイルは、提出前に Lean 4.22.0 で executable としてビルドして確認する。

## ドキュメント生成 (ローカル)

[doc-gen4](https://github.com/leanprover/doc-gen4) で API ドキュメントを生成する。
公開版は <https://kowerkoint.github.io/cplib-lean/Cplib.html> から参照できる。

付属スクリプトを使うのが簡単:

```sh
./scripts/make-docs.sh
```

生成物は `.lake/build/doc/` 以下に出力される。ブラウザで開くには:

```sh
xdg-open .lake/build/doc/Cplib.html   # 各モジュールは Cplib/<Name>.html
```

スクリプトはローカルのソースリンクを生成し、依存パッケージの互換性調整も行う。
初回は doc-gen4 本体もビルドするため時間がかかる。

## ライセンス

[MIT License](LICENSE)
