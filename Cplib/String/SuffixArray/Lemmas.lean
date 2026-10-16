import Cplib.String.SuffixArray.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace SuffixArray

example : suffixArray "abracadabra".toList.toArray = #[10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2] := by
  native_decide

example : suffixArray "mississippi".toList.toArray = #[10, 7, 4, 1, 0, 9, 8, 6, 3, 5, 2] := by
  native_decide

example : suffixArray #[3, 1, 4, 1, 5, 9, 2, 6] = #[1, 3, 6, 0, 2, 4, 7, 5] := by
  native_decide

/-- Counting-sort buckets cover inputs large enough to exercise every doubling round. -/
example : suffixArray (Array.range 256) = Array.range 256 := by
  native_decide

/-- Equal symbols are ordered by suffix length, including the radix sentinel key. -/
example : suffixArray (Array.replicate 128 0) = (Array.range 128).reverse := by
  native_decide

end SuffixArray
