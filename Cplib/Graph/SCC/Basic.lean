
namespace Cplib
/-!
# Graph.SCC.Basic

Decomposition into strongly connected components by Kosaraju's algorithm.

Vertices are `0, …, n - 1`, and the adjacency array is expected to satisfy
`g.size = n` with every listed neighbour below `n`. A malformed input still
terminates, because the searches are bounded by the vertex count, but the
components it returns are unspecified.

`scc` is `O(n + E)` for `E` edges in total.

```lean
scc 6 #[[1], [0, 2], [3], [2], [5], []]
-- [[4], [5], [0, 1], [2, 3]], components in topological order
```
-/

namespace SCC

namespace Impl

/-- Depth-first search, prepending vertices to `order` in reverse post-order.

`fuel` bounds the recursion depth. Passing the vertex count, together with never
recursing into a visited vertex, means the search is never cut short on a
well-formed input.
-/
def dfsPostOrderRev (fuel : Nat) (g : Array (List Nat))
    (seen : Array Bool) (order : List Nat) (u : Nat) : Array Bool × List Nat :=
  match fuel with
  | 0 => (seen, order)
  | fuel + 1 =>
      let (seen, order) := g[u]!.foldl (fun (seen, order) v =>
        if seen[v]! then (seen, order)
        else
          let seen := seen.set! v true
          dfsPostOrderRev fuel g seen order v
      ) (seen, order)
      (seen, u :: order)

def reverseGraph (n : Nat) (g : Array (List Nat)) : Array (List Nat) :=
  Nat.fold n (fun u _ rg =>
    g[u]!.foldl (fun rg v => rg.modify v (u :: ·)) rg
  ) (Array.replicate n [])

end Impl

/-- Decompose an `n`-vertex graph into its strongly connected components.

The components come back in topological order with respect to the edges between
them. Requires `g.size = n` and every neighbour below `n`. `O(n + E)`.
-/
def scc (n : Nat) (g : Array (List Nat)) : List (List Nat) :=
  let (_, postOrderRev) := Nat.fold n (fun u _ (seen, order) =>
    if seen[u]! then (seen, order)
    else Impl.dfsPostOrderRev n g (seen.set! u true) order u
  ) (Array.replicate n false, [])
  let rg := Impl.reverseGraph n g
  postOrderRev.foldl (fun (seen, components) u =>
    if seen[u]! then (seen, components)
    else
      let seen := seen.set! u true
      let (seen, component) := Impl.dfsPostOrderRev n rg seen [] u
      (seen, component :: components)
  ) (Array.replicate n false, []) |>.2.reverse

end SCC

export SCC (scc)

end Cplib
