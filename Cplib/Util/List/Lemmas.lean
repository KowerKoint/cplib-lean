import Cplib.Util.List.Basic
import Mathlib.Tactic

namespace List

/-- Run-length encoding keeps the product: an element that ran `k` times
contributes its `k`-th power. -/
theorem runLength_prod : ∀ l : List Nat,
    ((runLength l).map fun pe => pe.1 ^ pe.2).prod = l.prod := by
  intro l
  induction l with
  | nil => rfl
  | cons p rest ih =>
      rw [runLength]
      split
      · rename_i q e tail hsplit
        rw [hsplit] at ih
        simp only [List.map_cons, List.prod_cons] at ih
        split
        · rename_i hpq
          simp only [beq_iff_eq] at hpq
          subst hpq
          simp only [List.map_cons, List.prod_cons, Nat.pow_succ, List.prod_cons]
          rw [← ih]
          ring
        · simp only [List.map_cons, List.prod_cons]
          rw [← ih]
          ring
      · rename_i hsplit
        rw [hsplit] at ih
        simp only [List.map_nil, List.prod_nil] at ih
        simp only [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, ← ih]
        ring

example : [2, 2, 2, 3, 3, 5].runLength = [(2, 3), (3, 2), (5, 1)] := by native_decide

end List
