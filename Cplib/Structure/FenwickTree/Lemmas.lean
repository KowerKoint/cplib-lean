import Cplib.Structure.FenwickTree.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace Cplib

namespace FenwickTree

private theorem Impl.prefixFuel_replicate [AddMonoid α] (fuel i n : Nat) :
    Impl.prefixFuel (Vector.replicate n (0 : α)) fuel i = 0 := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
      cases i with
      | zero => rfl
      | succ i =>
          by_cases hi : i < n
          · simp [Impl.prefixFuel, ih, Vector.getD, Array.getD, hi]
          · simp [Impl.prefixFuel, ih, Vector.getD, Array.getD, hi]

@[simp] theorem empty_prefixSum [AddMonoid α] (i : Fin (n + 1)) :
    (empty n : FenwickTree α n).prefixSum i = 0 := by
  exact Impl.prefixFuel_replicate n i n

@[simp] theorem sum_self [AddGroup α] (self : FenwickTree α n) (i : Fin (n + 1)) :
    self.sum i i = 0 := by
  simp [sum]

@[simp] theorem empty_sum [AddGroup α] (l r : Fin (n + 1)) :
    (empty n : FenwickTree α n).sum l r = 0 := by
  simp [sum]

@[simp] theorem empty_get [AddGroup α] (i : Fin n) :
    (empty n : FenwickTree α n).get i = 0 := by
  simp [get]

example :
    let tree := ofArray #[3, 1, 4, 1, 5]
    tree.prefixSum 4 == 9 && tree.sum 1 4 == 6 &&
      (tree.add ⟨2, by decide⟩ 10).get ⟨2, by decide⟩ == 14 := by
  native_decide

end FenwickTree

end Cplib
