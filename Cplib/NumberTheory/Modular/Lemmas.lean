import Cplib.NumberTheory.Modular.Basic
import Mathlib.Tactic

namespace NumberTheory

@[simp] theorem powMod_modulus_zero (a e : Nat) : powMod a e 0 = 0 := rfl

@[simp] theorem powMod_exponent_zero (a m : Nat) (hm : 0 < m) :
    powMod a 0 m = 1 % m := by
  simp [powMod, Impl.powModFuel, Nat.ne_of_gt hm]

@[simp] theorem invMod?_modulus_zero (a : Nat) : invMod? a 0 = none := rfl

example : powMod 2 10 1_000_000_007 = 1024 := by native_decide
example : powMod 123456789 987654321 998244353 = 730701112 := by native_decide
example : invMod? 3 11 = some 4 := by native_decide
example : invMod? 6 15 = none := by native_decide

@[simp] theorem crt_empty : crt #[] = some (0, 1) := rfl

example : crt #[(2, 3), (3, 5), (2, 7)] = some (23, 105) := by native_decide
example : crt #[(1, 4), (3, 6)] = some (9, 12) := by native_decide
example : crt #[(1, 2), (0, 4)] = none := by native_decide
example : crt #[(-1, 5), (1, 3)] = some (4, 15) := by native_decide

end NumberTheory
