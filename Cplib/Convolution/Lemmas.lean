import Cplib.Convolution.Basic
import Mathlib.Tactic

namespace Cplib

namespace Convolution

def naive (modulus : Nat) (xs ys : Array Nat) : Array Nat :=
  if xs.isEmpty || ys.isEmpty then #[]
  else
    (Array.range (xs.size + ys.size - 1)).map fun k =>
      Nat.fold xs.size (fun i _ total =>
        if h : i ≤ k ∧ k - i < ys.size then
          (total + xs.getD i 0 * ys[k - i]) % modulus
        else total) 0

@[simp] theorem convolution_empty_left (ys : Array Nat) : convolution #[] ys = #[] := rfl
@[simp] theorem convolution_empty_right (xs : Array Nat) : convolution xs #[] = #[] := by
  simp [convolution, convolutionMod]

example : convolution #[1, 2, 3] #[4, 5] = #[4, 13, 22, 15] := by native_decide

example :
    let xs := (Array.range 64).map (fun x => (x * x + 7) % 998244353)
    let ys := (Array.range 57).map (fun x => (3 * x + 11) % 998244353)
    convolution xs ys = naive 998244353 xs ys := by
  native_decide

end Convolution

end Cplib
