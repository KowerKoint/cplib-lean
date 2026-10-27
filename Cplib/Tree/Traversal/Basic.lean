/-!
# Tree.Traversal.Basic

Depth-first search on a tree given as a bidirectional adjacency list, plus the
usual tree-DP utilities built on it.

Every vertex of an `n`-vertex tree appears as an index into `g`, so `g.size`
must be `n` and every neighbour must be below it. The search is bounded by
`g.size`, so a malformed input still terminates, but it may then visit a vertex
more than once.

All of `dfs`, `preorder`, `postorder`, `subtreeSize`, `depth` and `height` are
`O(n)`.

```lean
let g := #[[1, 2], [0], [0, 3], [2]]   -- 0—1, 0—2, 2—3
Tree.preorder g       -- [0, 1, 2, 3]
Tree.subtreeSize g    -- #[4, 1, 2, 1]
Tree.depth g          -- #[0, 1, 1, 2]
```
-/

namespace Cplib.Tree

namespace Impl

/-- Fuel-bounded implementation behind `Cplib.Tree.dfs`. -/
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

/-- Depth-first search from `root` over the tree given by the bidirectional
adjacency list `g`.

`onDescend state parent child` runs just before entering a child subtree and
`onAscend state parent child` just after returning from it, so a value threaded
through both sees each edge twice, once in each direction.

Requires `root < g.size`, every neighbour below `g.size`, and `g` to describe a
connected undirected tree. Violating that still terminates, since `g.size`
bounds the recursion, but a vertex may then be visited more than once. `O(n)`.
-/
def dfs
    (g : Array (List Nat))
    (init : α)
    (root : Nat := 0)
    (onDescend : α → Nat → Nat → α := fun x _ _ => x)
    (onAscend : α → Nat → Nat → α := fun x _ _ => x) : α :=
  Impl.dfs g onDescend onAscend g.size init root g.size

/-- Vertices in the order a DFS from `root` first reaches them (pre-order).
`O(n)`. -/
def preorder (g : Array (List Nat)) (root := 0) : List Nat :=
  dfs g [root] (root := root) (onDescend := fun res _ v => v :: res) |>.reverse

/-- Vertices in the order a DFS from `root` finishes them (post-order). `O(n)`. -/
def postorder (g : Array (List Nat)) (root := 0) : List Nat :=
  dfs g [] (root := root) (onAscend := fun res _ v => v :: res) |> (root :: ·) |>.reverse

/-- Number of vertices in each subtree, with the tree rooted at `root`. The root's
entry is the whole vertex count. `O(n)`. -/
def subtreeSize (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 1) (onAscend := fun res u v =>
    let szv := res[v]!
    res.modify u (· + szv))

/-- Number of edges from `root` to each vertex, with the tree rooted at `root`.
The root's entry is `0`. `O(n)`. -/
def depth (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 0) (onDescend := fun res u v =>
    let du := res[u]!
    res.set! v (du + 1))

/-- Height of each subtree, with the tree rooted at `root`, measured in edges so
that a leaf has height `0`. `O(n)`. -/
def height (g : Array (List Nat)) (root := 0) : Array Nat :=
  dfs g (root := root) (Array.replicate g.size 0) (onAscend := fun res u v =>
    let hv := res[v]!
    res.modify u (max · (hv + 1)))

end Cplib.Tree
