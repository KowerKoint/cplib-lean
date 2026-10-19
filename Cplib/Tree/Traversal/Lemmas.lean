import Cplib.Tree.Traversal.Basic
import Mathlib.Tactic

/-!
# Tree.Traversal.Lemmas

木の DFS と基本的な木 DP ユーティリティの性質。
-/

namespace Cplib.Tree

/-- 降下時と上昇時の更新が不変条件 `P` を保つなら、fuel 付き DFS も `P` を保つ。 -/
theorem Impl.dfs_preserves (g : Array (List Nat))
    (onDescend onAscend : α → Nat → Nat → α) (P : α → Prop)
    (hDescend : ∀ x u v, P x → P (onDescend x u v))
    (hAscend : ∀ x u v, P x → P (onAscend x u v))
    (fuel : Nat) (x : α) (u parent : Nat) (hx : P x) :
    P (Impl.dfs g onDescend onAscend fuel x u parent) := by
  induction fuel generalizing x u parent with
  | zero => exact hx
  | succ fuel ihFuel =>
      simp only [Impl.dfs]
      induction g[u]! generalizing x with
      | nil => exact hx
      | cons v vs ihList =>
          simp only [List.foldl_cons]
          apply ihList
          split
          · exact hx
          · exact hAscend _ _ _ (ihFuel _ _ _ (hDescend _ _ _ hx))

/-- 降下時と上昇時の更新が不変条件 `P` を保つなら、`Cplib.Tree.dfs` も `P` を保つ。 -/
theorem dfs_preserves (g : Array (List Nat)) (init : α) (root : Nat)
    (onDescend onAscend : α → Nat → Nat → α) (P : α → Prop)
    (hDescend : ∀ x u v, P x → P (onDescend x u v))
    (hAscend : ∀ x u v, P x → P (onAscend x u v))
    (hinit : P init) :
    P (dfs g init root onDescend onAscend) := by
  exact Impl.dfs_preserves g onDescend onAscend P hDescend hAscend
    g.size init root g.size hinit

@[simp] theorem subtreeSize_size (g : Array (List Nat)) (root : Nat) :
    (subtreeSize g root).size = g.size := by
  unfold subtreeSize
  apply dfs_preserves (P := fun xs : Array Nat => xs.size = g.size) <;> simp

@[simp] theorem depth_size (g : Array (List Nat)) (root : Nat) :
    (depth g root).size = g.size := by
  unfold depth
  apply dfs_preserves (P := fun xs : Array Nat => xs.size = g.size) <;> simp

@[simp] theorem height_size (g : Array (List Nat)) (root : Nat) :
    (height g root).size = g.size := by
  unfold height
  apply dfs_preserves (P := fun xs : Array Nat => xs.size = g.size) <;> simp

/-- 分岐を含む木における DFS 順と基本的な木 DP の回帰テスト。 -/
example :
    let g := #[[1, 2], [0, 3], [0], [1]]
    preorder g = [0, 1, 3, 2] ∧
    postorder g = [3, 1, 2, 0] ∧
    subtreeSize g = #[4, 2, 1, 1] ∧
    depth g = #[0, 1, 1, 2] ∧
    height g = #[2, 1, 0, 0] := by
  native_decide

end Cplib.Tree
