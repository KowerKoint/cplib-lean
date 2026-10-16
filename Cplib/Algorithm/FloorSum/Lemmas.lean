import Cplib.Algorithm.FloorSum.Basic
import Mathlib.Tactic

namespace FloorSum

@[simp] theorem floorSum_zero_modulus (n a b : Nat) :
    floorSum n 0 a b = 0 := rfl

private theorem Impl.floorSumFuel_zero_n (fuel m a b : Nat) :
    Impl.floorSumFuel fuel 0 m a b = 0 := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases m <;> simp [Impl.floorSumFuel, Nat.mod_lt]

@[simp] theorem floorSum_zero_count (m a b : Nat) :
    floorSum 0 m a b = 0 := by
  exact Impl.floorSumFuel_zero_n (m + 1) m a b

example : floorSum 4 10 6 3 = 3 := by native_decide
example : floorSum 6 7 4 3 = 9 := by native_decide
example : floorSum 1_000_000_000 998244353 123456789 987654321 =
    61836958798006594 := by native_decide

end FloorSum
