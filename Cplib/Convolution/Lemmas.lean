import Cplib.Convolution.Basic
import Mathlib.Tactic

namespace Cplib

namespace Convolution

def naive [NeZero modulus] (xs ys : Array (ModInt modulus)) : Array (ModInt modulus) :=
  if xs.isEmpty || ys.isEmpty then #[]
  else
    (Array.range (xs.size + ys.size - 1)).map fun k =>
      Nat.fold xs.size (fun i _ total =>
        if h : i ≤ k ∧ k - i < ys.size then
          total + xs.getD i 0 * ys[k - i]
        else total) 0

@[simp] theorem convolution_empty_left (ys : Array (ModInt 998244353)) :
    convolution #[] ys = #[] := rfl

@[simp] theorem convolution_empty_right (xs : Array (ModInt 998244353)) :
    convolution xs #[] = #[] := by
  simp [convolution, convolutionMod]

example : convolution #[1, 2, 3] #[4, 5] = #[4, 13, 22, 15] := by
  native_decide

example :
    let xs : Array (ModInt 998244353) :=
      (Array.range 64).map (fun x => ModInt.ofNat (x * x + 7))
    let ys : Array (ModInt 998244353) :=
      (Array.range 57).map (fun x => ModInt.ofNat (3 * x + 11))
    convolution xs ys = naive xs ys := by
  native_decide

end Convolution

end Cplib
