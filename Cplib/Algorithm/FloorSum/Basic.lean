namespace FloorSum

namespace Impl

def floorSumFuel : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | fuel + 1, n, m, a, b =>
      if m = 0 then 0
      else
        let ans := n * (n - 1) / 2 * (a / m) + n * (b / m)
        let a := a % m
        let b := b % m
        let y := a * n + b
        if y < m then ans
        else ans + floorSumFuel fuel (y / m) a m (y % m)

end Impl

/-- `∑ i ∈ [0, n), (a * i + b) / m` for natural numbers.

Returns `0` for the otherwise undefined case `m = 0`. For positive `m`, this
is the Euclidean-algorithm implementation used by competitive-programming
libraries and runs in logarithmic time.
-/
def floorSum (n m a b : Nat) : Nat :=
  Impl.floorSumFuel (m + 1) n m a b

end FloorSum
