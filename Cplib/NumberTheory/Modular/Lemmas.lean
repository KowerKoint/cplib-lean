import Cplib.NumberTheory.Modular.Basic
import Mathlib.Tactic

namespace Cplib

namespace NumberTheory

@[simp] theorem powMod_modulus_zero (a e : Nat) : powMod a e 0 = 0 := rfl

/-- Binary exponentiation computes the power, as long as the fuel outlasts the
exponent. -/
theorem Impl.powModFuel_eq {m : Nat} (_hm : 0 < m) (fuel : Nat) :
    ∀ b e : Nat, e < fuel → Impl.powModFuel m fuel b e = b ^ e % m := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
      intro b e he
      match e with
      | 0 => simp [Impl.powModFuel]
      | e + 1 =>
          rw [Impl.powModFuel, ih b ((e + 1) / 2) (by omega)]
          have hsquare : b ^ ((e + 1) / 2) % m * (b ^ ((e + 1) / 2) % m) % m =
              b ^ (2 * ((e + 1) / 2)) % m := by
            rw [← Nat.mul_mod, ← Nat.pow_add]
            congr 2
            omega
          rcases Nat.even_or_odd (e + 1) with heven | hodd
          · have hhalf : 2 * ((e + 1) / 2) = e + 1 := by
              have := Nat.even_iff.mp heven
              omega
            rw [if_pos (Nat.even_iff.mp heven), hsquare, hhalf]
          · have hhalf : 2 * ((e + 1) / 2) + 1 = e + 1 := by
              have := Nat.odd_iff.mp hodd
              omega
            rw [if_neg (by rw [Nat.odd_iff.mp hodd]; omega), hsquare, ← Nat.mul_mod,
              ← Nat.pow_succ, Nat.succ_eq_add_one, hhalf]

/-- `powMod` is the power modulo the modulus. -/
theorem powMod_eq (b e : Nat) {m : Nat} (hm : 0 < m) : powMod b e m = b ^ e % m := by
  rw [powMod, if_neg (by omega)]
  exact Impl.powModFuel_eq hm (e + 1) b e (by omega)

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

end Cplib
