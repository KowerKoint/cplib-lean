import Cplib.Typical.LinearSearch.Basic
import Mathlib.Tactic

namespace Cplib

/-- `findMinFrom` の完全仕様。`i + fuel = n` を保って呼ぶ前提で、結果は
`[i, n]` に収まり、`i` 以上その手前までは `p` を満たさず、`n` 未満なら `p` を満たす。 -/
theorem Impl.findMinFrom_spec (n : Nat) (p : Fin n → Bool) (i : Nat) :
    i ≤ Impl.findMinFrom n p i ∧ Impl.findMinFrom n p i ≤ max i n
      ∧ (∀ j : Fin n, i ≤ j.val → j.val < Impl.findMinFrom n p i → ¬p j)
      ∧ (∀ h : Impl.findMinFrom n p i < n, p ⟨Impl.findMinFrom n p i, h⟩) := by
  induction i using Impl.findMinFrom.induct (n := n) (p := p) with
  | case1 i hi hp =>
      rw [Impl.findMinFrom, dif_pos hi, if_pos hp]
      refine ⟨Nat.le_refl _, by omega, ?_, ?_⟩
      · intro j _ hj
        omega
      · intro _
        exact hp
  | case2 i hi hp ih =>
      rw [Impl.findMinFrom, dif_pos hi, if_neg hp]
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨by omega, by omega, ?_, h4⟩
      intro j hij hjr
      rcases Nat.lt_or_ge j.val (i + 1) with hj | hj
      · have hji : j = (⟨i, hi⟩ : Fin n) := Fin.ext (show j.val = i by omega)
        subst hji
        exact hp
      · exact h3 j hj hjr
  | case3 i hi =>
      rw [Impl.findMinFrom, dif_neg hi]
      refine ⟨Nat.le_refl _, by omega, ?_, ?_⟩
      · intro j _ hj
        omega
      · intro h
        omega

theorem findMinBelow_le (n : Nat) (p : Fin n → Bool) : findMinBelow n p ≤ n := by
  simpa using (Impl.findMinFrom_spec n p 0).2.1

/-- 手前の添字はどれも `p` を満たさない。 -/
theorem findMinBelow_not_of_lt (n : Nat) (p : Fin n → Bool) (i : Fin n)
    (h : i.val < findMinBelow n p) : ¬p i :=
  (Impl.findMinFrom_spec n p 0).2.2.1 i (Nat.zero_le _) h

/-- `n` 未満を返したなら、その添字は `p` を満たす。 -/
theorem findMinBelow_sat (n : Nat) (p : Fin n → Bool) (h : findMinBelow n p < n) :
    p ⟨findMinBelow n p, h⟩ :=
  (Impl.findMinFrom_spec n p 0).2.2.2 h

/-- `n` が返るのは、`p` を満たす添字が一つも無いとき、かつそのときに限る。 -/
theorem findMinBelow_eq_iff (n : Nat) (p : Fin n → Bool) :
    findMinBelow n p = n ↔ ∀ i : Fin n, ¬p i := by
  constructor
  · intro hn i
    exact findMinBelow_not_of_lt n p i (by rw [hn]; exact i.isLt)
  · intro hall
    rcases Nat.lt_or_ge (findMinBelow n p) n with h | h
    · exact absurd (findMinBelow_sat n p h) (hall _)
    · have := findMinBelow_le n p
      omega

example : findMinBelow 10 (fun i => i.val * i.val > 20) = 5 := by native_decide
example : findMinBelow 10 (fun i => i.val > 100) = 10 := by native_decide
example : findMinBelow 0 (fun _ => true) = 0 := by native_decide
/-- 単調でない述語でも最小の添字を返す。 -/
example : findMinBelow 10 (fun i => i.val == 7 || i.val == 3) = 3 := by native_decide

end Cplib
