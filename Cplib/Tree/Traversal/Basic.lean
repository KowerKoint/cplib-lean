/-!
# Tree.Traversal.Basic

双方向隣接リストで表された木の DFS と、基本的な木 DP ユーティリティ。
-/

namespace Cplib.Tree

namespace Impl

/-- `Cplib.Tree.dfs` の fuel 付き内部実装。 -/
def dfs (g : Array (List Nat))
    (onDescend onAscend : α → Nat → Nat → α) :
    Nat → α → Nat → Nat → α
  | 0, x, _, _ => x
  | fuel + 1, x, u, parent =>
      g[u]!.foldl (fun x v =>
        if v = parent then x
        else
          let x := onDescend x u v
          let x := dfs g onDescend onAscend fuel x v u
          onAscend x u v
      ) x

end Impl

/-- 双方向隣接リスト `g` で表された木を `root` から深さ優先探索する。

`onDescend state parent child` は子部分木へ入る直前、
`onAscend state parent child` は子部分木から戻った直後に呼ばれる。

`root < g.size` であり、各隣接先が `g.size` 未満で、`g` が連結な無向木を
表すことを要求する。この条件を満たさない場合も `g.size` を fuel として停止するが、
同じ頂点を複数回訪問することがある。
-/
def dfs
    (g : Array (List Nat))
    (init : α)
    (root : Nat := 0)
    (onDescend : α → Nat → Nat → α := fun x _ _ => x)
    (onAscend : α → Nat → Nat → α := fun x _ _ => x) : α :=
  Impl.dfs g onDescend onAscend g.size init root g.size

/-- `root` から DFS したときの行きがけ順。 -/
def preorder (g : Array (List Nat)) (root := 0) : List Nat :=
  dfs g [root] (root := root) (onDescend := fun res _ v => v :: res) |>.reverse

/-- `root` から DFS したときの帰りがけ順。 -/
def postorder (g : Array (List Nat)) (root := 0) : List Nat :=
  dfs g [] (root := root) (onAscend := fun res _ v => v :: res) |> (root :: ·) |>.reverse

/-- `root` で根付き木としたときの、各頂点の部分木の頂点数。 -/
def subtreeSize (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 1) (onAscend := fun res u v =>
    let szv := res[v]!
    res.modify u (· + szv))

/-- `root` で根付き木としたときの、`root` から各頂点までの距離。 -/
def depth (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 0) (onDescend := fun res u v =>
    let du := res[u]!
    res.set! v (du + 1))

/-- `root` で根付き木としたときの、各頂点を根とする部分木の高さ。 -/
def height (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 0) (onAscend := fun res u v =>
    let hv := res[v]!
    res.modify u (max · (hv + 1)))

end Cplib.Tree
