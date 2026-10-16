import Cplib.String.ZAlgorithm.Basic
import Mathlib.Tactic

namespace ZAlgorithm

@[simp] theorem zAlgorithm_size [BEq α] (xs : Array α) :
    (zAlgorithm xs).size = xs.size := by
  unfold zAlgorithm
  split <;> simp_all

@[simp] theorem zAlgorithm_empty [BEq α] : zAlgorithm (#[] : Array α) = #[] := rfl

example : zAlgorithm "ababa".toList.toArray = #[5, 0, 3, 0, 1] := by
  native_decide

example : zAlgorithm "aaaaa".toList.toArray = #[5, 4, 3, 2, 1] := by
  native_decide

example : zAlgorithm "aabcaabxaaaz".toList.toArray =
    #[12, 1, 0, 0, 3, 1, 0, 0, 2, 2, 1, 0] := by
  native_decide

end ZAlgorithm
