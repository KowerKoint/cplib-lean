import Cplib.NumberTheory.ModInt.Basic
import Mathlib.Tactic

/-!
# NumberTheory.ModInt.Lemmas

固定法剰余数型の基本的な性質。
-/

namespace Cplib.ModInt

@[ext] theorem ext {a b : ModInt modulus} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem val_ofNat [NeZero modulus] (value : Nat) :
    (ofNat value : ModInt modulus).val = value % modulus := rfl

@[simp] theorem val_zero [NeZero modulus] : (0 : ModInt modulus).val = 0 := by
  simp [OfNat.ofNat, ofNat, Nat.mod_eq_of_lt (Nat.pos_of_neZero modulus)]

@[simp] theorem val_one [NeZero modulus] : (1 : ModInt modulus).val = 1 % modulus := rfl

/-- 加算は通常の和を法で割った余りと一致する。 -/
@[simp] theorem val_add (a b : ModInt modulus) :
    (a + b).val = (a.val + b.val) % modulus := by
  change (ModInt.add a b).val = _
  simp only [ModInt.add]
  split
  next h => exact (Nat.mod_eq_of_lt h).symm
  next h =>
    rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt h)]
    rw [Nat.mod_eq_of_lt]
    have ha := a.isLt
    have hb := b.isLt
    omega

/-- 減算の内部値は、大小関係に応じて1回の減算または加算で求められる。 -/
@[simp] theorem val_sub (a b : ModInt modulus) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + (modulus - b.val) := by
  change (ModInt.sub a b).val = _
  simp only [ModInt.sub]
  split <;> simp_all

/-- 符号反転の内部値。 -/
@[simp] theorem val_neg (a : ModInt modulus) :
    (-a).val = if a.val = 0 then a.val else modulus - a.val := by
  change (ModInt.neg a).val = _
  simp only [ModInt.neg]
  split <;> simp_all

/-- 乗算は通常の積を法で割った余りと一致する。 -/
@[simp] theorem val_mul (a b : ModInt modulus) :
    (a * b).val = a.val * b.val % modulus := rfl

example : ((1_000_000_006 : ModInt 1_000_000_007) + 2).val = 1 := by native_decide
example : ((0 : ModInt 1_000_000_007) - 1).val = 1_000_000_006 := by native_decide
example : ((123456789 : ModInt 998244353) * 987654321).val = 263684735 := by native_decide
example : ((2 : ModInt 1_000_000_007) ^ 10).val = 1024 := by native_decide
example : (3 : ModInt 11).inv?.map toNat = some 4 := by native_decide
example : (6 : ModInt 15).inv? = none := by native_decide
example : ((10 : ModInt 11) / 2).val = 5 := by native_decide
example : ((1 : ModInt 15) / 6).val = 0 := by native_decide

end Cplib.ModInt
