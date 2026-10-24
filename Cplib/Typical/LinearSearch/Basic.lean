namespace Cplib

/-!
# Typical.LinearSearch.Basic

上限付きの線形探索。述語が単調な場合は `Cplib.bisectMinBelow` が `O(log n)` で
同じ答えを返すので、こちらは単調でない述語のためにある。
-/

namespace Impl

/-- `findMinBelow` の内部実装。`i` から順に `p` を試し、`n` に達したら `n` を返す。

境界判定は一度だけで、`fuel` 引数は持たない (反復あたりの分岐を増やさないため)。 -/
@[specialize] def findMinFrom (n : Nat) (p : Fin n → Bool) (i : Nat) : Nat :=
  if h : i < n then
    if p ⟨i, h⟩ then i else findMinFrom n p (i + 1)
  else i
termination_by n - i
decreasing_by omega

end Impl

/-- `p` を満たす最小の `x < n`。存在しなければ `n` を返す。

`0, 1, …, n - 1` の順に調べ、最初に見つかった時点で打ち切る。確保は行わない。
`p` が単調 (false から true へ一度だけ変化) なら `bisectMinBelow` のほうが速い。 -/
@[inline] def findMinBelow (n : Nat) (p : Fin n → Bool) : Nat :=
  Impl.findMinFrom n p 0

end Cplib
