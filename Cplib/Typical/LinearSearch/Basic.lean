namespace Cplib

/-!
# Typical.LinearSearch.Basic

Bounded linear search for the first index satisfying a predicate.

This exists for predicates that are **not** monotone. When `p` does turn from
false to true exactly once, `Cplib.bisectMinBelow` answers the same question in
`O(log n)` instead.

The core library offers nothing for this: there is no `Nat.find`,
`Nat.findSome?` or `Fin.find`, `Std.Iterators` has producers and combinators
but no `find?` consumer, and `Nat.any` reports whether a witness exists but not
which one. Mathlib's `Nat.find` additionally demands a proof of `∃ n, p n`.

```lean
findMinBelow 10 (fun i => i.val * i.val > 20)   -- 5
findMinBelow 10 (fun i => i.val > 100)          -- 10, that is, not found
```
-/

namespace Impl

/-- Implementation behind `findMinBelow`. Tries `p` at `i`, `i + 1`, … and
returns `n` on reaching it.

There is no fuel argument: the bound doubles as the termination measure, so each
iteration performs a single comparison rather than two. -/
@[specialize] def findMinFrom (n : Nat) (p : Fin n → Bool) (i : Nat) : Nat :=
  if h : i < n then
    if p ⟨i, h⟩ then i else findMinFrom n p (i + 1)
  else i
termination_by n - i
decreasing_by omega

end Impl

/-- The least `x < n` with `p x = true`, or `n` when there is none.

Tries `0, 1, …, n - 1` in order and stops at the first hit, allocating nothing.
`O(n)` worst case, times the cost of `p`. Prefer `bisectMinBelow` when `p` is
monotone. -/
@[inline] def findMinBelow (n : Nat) (p : Fin n → Bool) : Nat :=
  Impl.findMinFrom n p 0

end Cplib
