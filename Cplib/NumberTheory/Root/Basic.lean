import Cplib.Typical.Bisect.Basic

namespace Cplib

/-!
# NumberTheory.Root.Basic

The floor of the `k`-th root of a natural number.

`n.iroot k` is the largest `x` with `x ^ k ≤ n`, found by binary search. The
powers along the way are computed with `Impl.powCap`, which stops climbing once
it passes `n`: without that, a search over `[0, n]` would build numbers as large
as `n ^ k`.

```lean
(1000 : Nat).iroot 3     -- 10
(999 : Nat).iroot 3      -- 9
(2 ^ 64 : Nat).iroot 2   -- 4294967296
```
-/

namespace NumberTheory
namespace Impl

/-- `a * b`, held down to `cap + 1` once it passes `cap`. -/
def mulCap (cap a b : Nat) : Nat := min (a * b) (cap + 1)

/-- `x ^ k`, held down to `cap + 1` once it passes `cap`.

Binary exponentiation that saturates at every step, so the numbers multiplied
stay below `(cap + 1)²` however large `x ^ k` would be. -/
def powCap (cap x : Nat) : Nat → Nat
  | 0 => min 1 (cap + 1)
  | k + 1 =>
      let half := powCap cap x ((k + 1) / 2)
      let square := mulCap cap half half
      if (k + 1) % 2 = 0 then square else mulCap cap square x
decreasing_by omega

end Impl
end NumberTheory

end Cplib

namespace Nat

/-- The floor of the `k`-th root of `n`: the largest `x` with `x ^ k ≤ n`.

No `x` is largest when `k = 0`, since `x ^ 0 = 1` for every `x`; `n.iroot 0` is
`0`.

`O(log n)` steps of binary search, each a capped power costing `O(log k)`
multiplications. -/
def iroot (n k : Nat) : Nat :=
  if k = 0 then 0
  else Cplib.bisectMax' 0 (n + 1) fun x => Cplib.NumberTheory.Impl.powCap n x k ≤ n

end Nat
