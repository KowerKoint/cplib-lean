import Cplib.Graph.SCC.Basic
import Mathlib.Tactic

/-!
# Graph.SCC.Lemmas

強連結成分分解の仕様と補題。
-/

namespace SCC

/-- 隣接リストが `n` 頂点のグラフとして整形式であること。 -/
def ValidInput (n : Nat) (g : Array (List Nat)) : Prop :=
  g.size = n ∧ ∀ u, u < n → ∀ v ∈ g[u]!, v < n

@[simp] theorem scc_zero (g : Array (List Nat)) : scc 0 g = [] := by
  simp [scc, Impl.reverseGraph]

@[simp] theorem reverseGraph_size (n : Nat) (g : Array (List Nat)) :
    (Impl.reverseGraph n g).size = n := by
  have inner (u : Nat) (vs : List Nat) (rg : Array (List Nat)) :
      (vs.foldl (fun rg v => rg.modify v (u :: ·)) rg).size = rg.size := by
    induction vs generalizing rg with
    | nil => rfl
    | cons v vs ih =>
        simp only [List.foldl_cons]
        rw [ih]
        simp
  have outer (us : List Nat) (rg : Array (List Nat)) :
      (us.foldl (fun rg u =>
        g[u]!.foldl (fun rg v => rg.modify v (u :: ·)) rg) rg).size = rg.size := by
    induction us generalizing rg with
    | nil => rfl
    | cons u us ih =>
        simp only [List.foldl_cons]
        rw [ih, inner]
  simp only [Impl.reverseGraph]
  rw [outer]
  simp

/-- 孤立した各頂点はそれぞれ一つの強連結成分になる。 -/
example : scc 3 #[[], [], []] = [[2], [1], [0]] := by
  native_decide

/-- 一つの有向閉路は一つの強連結成分になる。 -/
example : scc 3 #[[1], [2], [0]] = [[0, 2, 1]] := by
  native_decide

/-- 複数成分を、成分間の辺に関するトポロジカル順で返す。 -/
example : scc 6 #[[1], [0, 2], [3], [2], [5], []] =
    [[4], [5], [0, 1], [2, 3]] := by
  native_decide

end SCC
