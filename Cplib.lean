-- Utilities
import Cplib.Util.Number
import Cplib.Util.Container

-- Algorithms
import Cplib.Algorithm.Bisect
import Cplib.Algorithm.FloorSum
import Cplib.Algorithm.String

-- Graph algorithms
import Cplib.Graph

-- Data structures
import Cplib.Structure.Heap
import Cplib.Structure.SegTree
import Cplib.Structure.FenwickTree
import Cplib.Structure.UnionFind

/-!
# Cplib

競技プログラミング向けのアルゴリズム / データ構造ライブラリ。
Lean 4.22.0 (AtCoder と同一) でビルドできるモジュールをここに集約する。

ファイル構成は `Std` / `Batteries` の慣習に倣う:

- `Cplib.<分類>.<名前>.Basic` … 実装。他の `Basic` のみに依存し、`Mathlib` は引かない。
- `Cplib.<分類>.<名前>.Lemmas` … 定理。`Basic` と証明用の依存 (`Mathlib` 等) を import する。
- `Cplib.<分類>.<名前>` … 上記をまとめて読み込む集約モジュール (このルートが import するもの)。

実装だけを軽く使いたい場合 (AtCoder 提出など) は `...Basic` を直接 import すると、
`Lemmas` (および `Mathlib`) を引かずにビルドできる。

-/
