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
  未証明でもよい。例えば `SegTree.get` の性質は証明しても、`get!` や `get?` について同様の定理を
  個別には用意しないことがある。

## 構成

`Std` / `Batteries` の慣習に倣い、実装と定理をモジュール単位で分割している。

```
Cplib.lean                          ルート (各集約モジュールを import)
Cplib/
  Util/
    Number.lean                     中点計算と区間縮小補題 (実装と不可分のため非分割)
    Container.lean                  集約: Basic + Lemmas
    Container/Basic.lean            uniqueSorted / prefixSum (実装)
    Container/Lemmas.lean           Container の定理 (現状スタブ)
  Algorithm/
    Bisect.lean                     集約: Basic + Lemmas
    Bisect/Basic.lean               二分探索 / lowerBound / upperBound (実装)
    Bisect/Lemmas.lean              Bisect の定理 (現状スタブ)
  Structure/
    Heap.lean                       集約: Basic + Lemmas
    Heap/Basic.lean                 二分ヒープ (実装)
    Heap/Lemmas.lean                Heap の定理 (現状スタブ)
    SegTree.lean / SegTree/{Basic,Lemmas}.lean          セグメント木
```

ファイル分割の方針 (`Std.Data.HashMap.{Basic,Lemmas}` と同じ):

- `Cplib.<分類>.<名前>.Basic` … 実装。他の `Basic` のみに依存し、**`Mathlib` を import しない**。
- `Cplib.<分類>.<名前>.Lemmas` … 定理。`Basic` と証明用の依存 (`Mathlib` 等) を import する。
- `Cplib.<分類>.<名前>` … 上記をまとめて読み込む集約モジュール。`Cplib.lean` はこれを import する。

**実装だけを軽く使いたい場合 (AtCoder 提出など) は `...Basic` を直接 import する。**
`Lemmas` (および `Mathlib`) を引かないのでビルドが速い。実装を編集したときの再ビルドも、
`Basic` が `Mathlib` 非依存なので軽い。

- 4.22.0 でビルドできない作業中の証明は `Wip` ライブラリに隔離する。`defaultTargets`
  に含めていないため、`lake build` (= 既定ビルド) は常にグリーンを保つ。移植が済んだ証明は
  対応する `Lemmas` へ移す。

## ビルド

```sh
# 依存解決 (初回・依存更新時)
lake update

# Mathlib のビルド済みキャッシュを取得 (初回ビルドを高速化)
lake exe cache get

# 実装ライブラリのビルド (既定ターゲット)
lake build

# 作業中の証明の移植状況を確認 (現状は失敗する想定)
lake build Wip
```

## AtCoder 用の単一ファイル生成

`scripts/bundle.py` はエントリファイルから到達可能な `Cplib.*` import を依存順に
展開する。AtCoder 側に存在する Mathlib / Std などの import は先頭に残す。

```sh
python3 scripts/bundle.py ../atc/Main.lean -o ../atc/Submit.lean
```

通常は `atc/` 側の `make submit` を使う。生成後のファイルは必ず Lean 4.22.0 で
executable としてビルドしてから提出する。

## ドキュメント生成 (ローカル)

[doc-gen4](https://github.com/leanprover/doc-gen4) で API ドキュメントを生成する。
付属スクリプトを使うのが簡単:

```sh
./scripts/make-docs.sh
```

生成物は `.lake/build/doc/` 以下に出力される。ブラウザで開くには:

```sh
xdg-open .lake/build/doc/Cplib.html   # 各モジュールは Cplib/<Name>.html
```

### この環境固有の注意点

スクリプトは以下の 2 点を自動で処理している。直接 `lake build Cplib:docs` を叩く場合は手動対応が必要:

1. **`DOCGEN_SRC=file`** … doc-gen4 は既定でソースリンクを GitHub リモートから解決するが、
   ローカル生成では git remote が無いと失敗する。`DOCGEN_SRC=file` でローカル `file://`
   リンクに切り替える。GitHub Pages 等で公開する際は `DOCGEN_SRC=github` + git remote 設定に変更する。
2. **UnicodeBasic の `precompileModules` 無効化** … doc-gen4 依存の `UnicodeBasic` は、この環境では
   `precompileModules := true` だと外部 C シンボル (`unicode_case_lookup`) を解決できず `.so` 読み込みに失敗する。
   `.lake/packages/UnicodeBasic/lakefile.lean` で `false` に変更すると解消する
   (`lake update` で元に戻るため、スクリプトが都度適用する)。

> 注: 初回は doc-gen4 本体のビルドも走るため時間がかかる。

## ライセンス

[MIT License](LICENSE)
