
namespace Cplib
/-!
# Graph.SCC.Basic

Kosaraju 法による強連結成分分解。
頂点は `0, ..., n - 1` で表し、隣接リスト中の頂点もこの範囲にあることを仮定する。
-/

namespace SCC

namespace Impl

/-- 深さ優先探索を行い、帰りがけ順を逆順で `order` に追加する。

`fuel` は再帰の深さを制限する。頂点数を渡し、訪問済み頂点へ再帰しないことで、
正しい入力上では探索を打ち切らない。
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

/-- `n` 頂点のグラフを強連結成分に分解する。

返される成分は、成分間の辺に関するトポロジカル順に並ぶ。
`g.size = n` かつ全ての隣接先が `n` 未満であることを要求する。
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
