import Cplib.NumberTheory.Root.Basic
import Cplib.Typical.Bisect.Lemmas
import Mathlib.Tactic

namespace Cplib

/-!
# NumberTheory.Root.Lemmas

Specification of `Nat.iroot`.

`Nat.le_iroot_iff` is the characterisation to reach for: below a positive `k`,
`x ≤ n.iroot k` and `x ^ k ≤ n` say the same thing. The two bounds it is built
from, `Nat.iroot_pow_le` and `Nat.lt_iroot_succ_pow`, are stated too.

The capped power the search runs on answers the same comparisons as the real
one: `Impl.powCap_eq` pins it to `min (x ^ k) (cap + 1)`.
-/

namespace NumberTheory
namespace Impl

theorem mulCap_comm (cap a b : Nat) : mulCap cap a b = mulCap cap b a := by
  unfold mulCap; rw [Nat.mul_comm]

theorem mulCap_min_left (cap a b : Nat) :
    mulCap cap (min a (cap + 1)) b = min (a * b) (cap + 1) := by
  unfold mulCap
  rcases Nat.lt_or_ge a (cap + 1) with h | h
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right h]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h1 : cap + 1 ≤ (cap + 1) * b := Nat.le_mul_of_pos_right _ hb
      have h2 : cap + 1 ≤ a * b := Nat.le_trans h1 (Nat.mul_le_mul_right b h)
      rw [Nat.min_eq_right h1, Nat.min_eq_right h2]

theorem mulCap_min (cap a b : Nat) :
    mulCap cap (min a (cap + 1)) (min b (cap + 1)) = min (a * b) (cap + 1) := by
  rw [mulCap_comm, mulCap_min_left]
  show mulCap cap b (min a (cap + 1)) = _
  rw [mulCap_comm, mulCap_min_left, Nat.mul_comm]

/-- The capped power is the real one, held down to `cap + 1`. -/
theorem powCap_eq (cap x k : Nat) : powCap cap x k = min (x ^ k) (cap + 1) := by
  fun_induction powCap cap x k with
  | case1 => simp
  | case2 a b c h ih =>
      show mulCap cap (powCap cap x ((a + 1) / 2)) (powCap cap x ((a + 1) / 2)) = _
      rw [ih, mulCap_min, ← Nat.pow_add]
      congr 2
      omega
  | case3 a b c h ih =>
      show mulCap cap (mulCap cap (powCap cap x ((a + 1) / 2)) (powCap cap x ((a + 1) / 2))) x = _
      rw [ih, mulCap_min, ← Nat.pow_add, mulCap_min_left, ← Nat.pow_succ]
      congr 2
      omega

/-- …so it answers the comparison the search asks of it. -/
theorem powCap_le_iff (cap x k : Nat) : powCap cap x k ≤ cap ↔ x ^ k ≤ cap := by
  rw [powCap_eq]
  omega

end Impl
end NumberTheory

end Cplib

namespace Nat

open Cplib Cplib.NumberTheory.Impl

@[simp] theorem iroot_zero (n : Nat) : n.iroot 0 = 0 := rfl

private theorem iroot_mono (n k : Nat) :
    monotoneTrueToFalse fun x => decide (powCap n x k ≤ n) := by
  intro x y hxy hy
  simp only [decide_eq_true_eq, powCap_le_iff] at hy ⊢
  exact Nat.le_trans (Nat.pow_le_pow_left hxy k) hy

private theorem iroot_spec (n : Nat) {k : Nat} (hk : 0 < k) :
    let res := n.iroot k
    (res ≤ n) ∧ ∀ x, 0 < x → x < n + 1 → (x ≤ res ↔ x ^ k ≤ n) := by
  have hres : n.iroot k = bisectMax' 0 (n + 1) fun x => decide (powCap n x k ≤ n) := by
    rw [iroot, if_neg (by omega)]
  obtain ⟨⟨-, hlt⟩, hspec⟩ :=
    bisectMax_spec (ok := 0) (ng := n + 1) (by omega) _ (iroot_mono n k)
  refine ⟨by omega, fun x hx hxn => ?_⟩
  have := hspec x hx hxn
  rw [← hres] at this hlt
  by_cases hle : x ≤ n.iroot k
  · rw [if_pos hle] at this
    simpa [powCap_le_iff] using ⟨fun _ => by simpa [powCap_le_iff] using this, fun _ => hle⟩
  · rw [if_neg hle] at this
    simp only [decide_eq_true_eq, powCap_le_iff] at this
    exact ⟨fun h => absurd h hle, fun h => absurd h this⟩

/-- The `k`-th root raised to the `k` does not pass `n`. -/
theorem iroot_pow_le (n : Nat) {k : Nat} (hk : 0 < k) : n.iroot k ^ k ≤ n := by
  obtain ⟨hle, hspec⟩ := iroot_spec n hk
  rcases Nat.eq_zero_or_pos (n.iroot k) with h0 | hpos
  · rw [h0, Nat.zero_pow (by omega)]
    exact Nat.zero_le n
  · exact (hspec _ hpos (by omega)).mp (Nat.le_refl _)

/-- …and one more does. -/
theorem lt_iroot_succ_pow (n : Nat) {k : Nat} (hk : 0 < k) : n < (n.iroot k + 1) ^ k := by
  obtain ⟨hle, hspec⟩ := iroot_spec n hk
  rcases Nat.lt_or_ge (n.iroot k) n with hlt | hge
  · by_contra hc
    exact absurd ((hspec (n.iroot k + 1) (by omega) (by omega)).mpr (by omega)) (by omega)
  · have : n.iroot k = n := by omega
    rw [this]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_self_pow (by omega) _)

/-- Below a positive `k`, `x ≤ n.iroot k` and `x ^ k ≤ n` say the same thing. -/
theorem le_iroot_iff {n k x : Nat} (hk : 0 < k) : x ≤ n.iroot k ↔ x ^ k ≤ n := by
  constructor
  · intro h
    exact Nat.le_trans (Nat.pow_le_pow_left h k) (iroot_pow_le n hk)
  · intro h
    by_contra hc
    have : n.iroot k + 1 ≤ x := by omega
    exact absurd (Nat.le_trans (Nat.pow_le_pow_left this k) h)
      (by have := lt_iroot_succ_pow n hk; omega)

@[simp] theorem iroot_one (n : Nat) : n.iroot 1 = n := by
  have h1 := iroot_pow_le n (k := 1) (by omega)
  have h2 := lt_iroot_succ_pow n (k := 1) (by omega)
  simp only [Nat.pow_one] at h1 h2
  omega

@[simp] theorem zero_iroot (k : Nat) : (0 : Nat).iroot k = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have h : (0 : Nat).iroot k ^ k = 0 := Nat.le_zero.mp (iroot_pow_le 0 hk)
    exact (Nat.pow_eq_zero.mp h).1

example : (1000 : Nat).iroot 3 = 10 := by native_decide
example : (999 : Nat).iroot 3 = 9 := by native_decide
example : (2 ^ 64 : Nat).iroot 2 = 2 ^ 32 := by native_decide
example : (10 ^ 18 : Nat).iroot 60 = 1 := by native_decide

end Nat
