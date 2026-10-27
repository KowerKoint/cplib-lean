import Cplib.Graph.SCC.Basic
import Cplib.Util.Fold.Lemmas
import Mathlib.Tactic

namespace Cplib

/-!
# Graph.SCC.Lemmas

Specification and lemmas for the strongly connected component decomposition.
-/

namespace SCC

/-- The adjacency array is well formed as an `n`-vertex graph. -/
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
  rw [Nat.fold_eq_foldl_range, outer]
  simp

/-- Each isolated vertex forms a component of its own. -/
example : scc 3 #[[], [], []] = [[2], [1], [0]] := by
  native_decide

/-- A single directed cycle forms one component. -/
example : scc 3 #[[1], [2], [0]] = [[0, 2, 1]] := by
  native_decide

/-- Several components come back in topological order with respect to the edges
between them. -/
example : scc 6 #[[1], [0, 2], [3], [2], [5], []] =
    [[4], [5], [0, 1], [2, 3]] := by
  native_decide

end SCC

end Cplib
