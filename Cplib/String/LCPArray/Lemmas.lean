import Cplib.String.LCPArray.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace LCPArray

private theorem Impl.loop_size [BEq α] (xs : Array α) (sa rank : Array Nat)
    (fuel i common : Nat) (lcp : Array Nat) :
    (Impl.loop xs sa rank fuel i common lcp).size = lcp.size := by
  induction fuel generalizing i common lcp with
  | zero => rfl
  | succ fuel ih =>
      rw [Impl.loop]
      split
      · dsimp only
        split
        · split <;> simp [ih]
        · exact ih _ _ _
      · rfl

@[simp] theorem lcpArray_size [BEq α] (xs : Array α) (sa : Array Nat) :
    (lcpArray xs sa).size = xs.size - 1 := by
  unfold lcpArray
  rw [Impl.loop_size]
  simp

example :
    suffixAndLCP "abracadabra".toList.toArray =
      (#[10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2], #[1, 4, 1, 1, 0, 3, 0, 0, 0, 2]) := by
  native_decide

example : suffixAndLCP "aaaaa".toList.toArray =
    (#[4, 3, 2, 1, 0], #[1, 2, 3, 4]) := by
  native_decide

end LCPArray
