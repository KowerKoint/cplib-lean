import Cplib.NumberTheory.Modular.Basic
import Cplib.NumberTheory.Root.Basic

namespace Cplib

/-!
# NumberTheory.Prime.Basic

Primality and factorisation for numbers far beyond what trial division reaches.

`isPrime` is the Miller-Rabin test over a fixed set of bases, which makes it
deterministic: no random source, and the same answer every time. Which bases
are enough depends on how large `n` is, and the three sets used here are the
ones that have been verified by exhaustive search:

| range | bases | checked by |
|---|---|---|
| `n < 4759123141` | `2, 7, 61` | Jaeschke 1993 |
| `n < 2 ^ 64` | `2, 325, 9375, 28178, 450775, 9780504, 1795265022` | Sinclair, see <https://miller-rabin.appspot.com/> |
| `n < 3317044064679887385961981` | the first twelve primes | Sorenson and Webster 2015 |

**Past `3.3 × 10^24` the answer is not a proof.** A composite that passes every
base in the last set would have to be larger than that bound, and none is
known, but none is ruled out either: there `isPrime` means *strong probable
prime*. Within the bounds above it is exact. `Prime.Lemmas` proves the half
that does not depend on those searches, that a prime passes every base.

`factorize` splits `n` by Pollard's rho with `f(x) = x² + c`, trying
`c = 1, 2, 3, …` in turn rather than drawing `c` at random, and calls `isPrime`
to decide when a part is done. It costs about `O(n ^ (1/4))` per factor: around 20 ms for a product of two
primes near `10 ^ 9`, where the time goes on `Nat` multiplications of numbers
that no longer fit a machine word.

```lean
isPrime 998244353                 -- true
isPrime (2 ^ 61 - 1)              -- true
factorize 1000000016000000063     -- #[(1000000007, 1), (1000000009, 1)]
primeFactors 360                  -- #[2, 2, 2, 3, 3, 5]
divisors 36                       -- #[1, 2, 3, 4, 6, 9, 12, 18, 36]
```
-/

namespace NumberTheory
namespace Impl

/-- The primes below 64, which every number is divided by before anything
cleverer is tried. They also settle every `n` smaller than `64 ^ 2`. -/
def smallPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

/-- Bases that decide `n < 4759123141` (Jaeschke 1993). -/
def smallBases : List Nat := [2, 7, 61]

/-- Bases that decide `n < 2 ^ 64` (Sinclair). -/
def wideBases : List Nat := [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

/-- Bases that decide `n < 3317044064679887385961981` (Sorenson and Webster
2015): the first twelve primes. -/
def hugeBases : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Split `m` into its odd part and the number of twos: `m = (oddPart m).1 * 2 ^ (oddPart m).2`. -/
def oddPart (m : Nat) : Nat × Nat :=
  if _h : m = 0 ∨ m % 2 = 1 then (m, 0)
  else
    let (d, s) := oddPart (m / 2)
    (d, s + 1)
decreasing_by omega

/-- Square `y` up to `s` times, asking each time whether it has reached `n - 1`. -/
def sprpLoop (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | s + 1, y => y == n - 1 || sprpLoop n s (y * y % n)

/-- Whether `n` is a strong probable prime to base `a`.

For an odd `n` greater than `2`, write `n - 1 = d * 2 ^ s` with `d` odd. A
prime leaves `a ^ d ≡ 1` or `a ^ (d * 2 ^ r) ≡ -1` for some `r < s`, because
the only square roots of `1` in a field are `1` and `-1`. -/
def isSprp (n a : Nat) : Bool :=
  let ds := oddPart (n - 1)
  let y := powMod a ds.1 n
  y == 1 || sprpLoop n ds.2 y

end Impl

/-- Whether `n` is prime, by Miller-Rabin over a fixed set of bases.

Exact for `n < 3317044064679887385961981`, and a strong probable prime test
beyond it; see the module docstring. `O(log n)` modular multiplications per
base, with at most twelve bases. -/
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if Impl.smallPrimes.any (fun p => n == p) then true
  else if Impl.smallPrimes.any (fun p => n % p == 0) then false
  else
    let bases :=
      if n < 4759123141 then Impl.smallBases
      else if n < 18446744073709551616 then Impl.wideBases
      else Impl.hugeBases
    bases.all (Impl.isSprp n)

namespace Impl

/-- One step of `f(x) = x² + c` modulo `n`. -/
def rhoStep (n c x : Nat) : Nat := (x * x + c) % n

/-- Floyd's two walkers over `f(x) = x² + c`, stopping at the first common
factor they expose.

`none` means this `c` led nowhere: either the walkers met, or the factor found
was `n` itself. -/
def rhoLoop (n c : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, x, y =>
      let d := Nat.gcd (n + y - x) n
      if d == 1 then rhoLoop n c fuel (rhoStep n c x) (rhoStep n c (rhoStep n c y))
      else if d == n then none
      else some d

/-- Run `rhoLoop` for `c`, `c + 1`, … until one of them gives a factor. -/
def findFactor (n steps : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | attempts + 1, c =>
      match rhoLoop n c steps c (rhoStep n c c) with
      | some d => some d
      | none => findFactor n steps attempts (c + 1)

/-- How far one `c` is walked: the cycle is expected after about `n ^ (1/4)`
steps, with room to spare. -/
def rhoSteps (n : Nat) : Nat := 4 * n.iroot 4 + 64

/-- How many values of `c` are tried before giving up. -/
def rhoAttempts : Nat := 64

/-- The prime factors of `n` with multiplicity, in no particular order.

`fuel` bounds how often the number is split; each split costs one. Out of fuel,
or out of values of `c`, the part that is left is returned as it stands, so the
product is right even when the factorisation is not complete. -/
def factorsAux (n : Nat) : Nat → List Nat
  | 0 => if n ≤ 1 then [] else [n]
  | fuel + 1 =>
      if n ≤ 1 then []
      else if isPrime n then [n]
      else
        match smallPrimes.find? (fun p => n % p == 0) with
        | some p => p :: factorsAux (n / p) fuel
        | none =>
            match findFactor n (rhoSteps n) rhoAttempts 1 with
            | some d => factorsAux d fuel ++ factorsAux (n / d) fuel
            | none => [n]

/-- Collect a sorted list of factors into `(factor, multiplicity)` pairs. -/
def runLength : List Nat → List (Nat × Nat)
  | [] => []
  | p :: rest =>
      match runLength rest with
      | (q, e) :: tail => if p == q then (q, e + 1) :: tail else (p, 1) :: (q, e) :: tail
      | [] => [(p, 1)]

end Impl

/-- The prime factors of `n` with multiplicity, in increasing order. `1` has no
factors, and neither has `0`.

About `O(n ^ (1/4))` per factor, by Pollard's rho; see the module docstring. -/
def primeFactors (n : Nat) : Array Nat :=
  ((Impl.factorsAux n (n + 1)).mergeSort (· ≤ ·)).toArray

/-- The prime factorisation of `n` as `(prime, exponent)` pairs, in increasing
order of prime. -/
def factorize (n : Nat) : Array (Nat × Nat) :=
  (Impl.runLength ((Impl.factorsAux n (n + 1)).mergeSort (· ≤ ·))).toArray

namespace Impl

/-- Multiply every divisor so far by every power of `p` up to `p ^ e`. -/
def divisorStep (acc : List Nat) (pe : Nat × Nat) : List Nat :=
  (List.range (pe.2 + 1)).flatMap fun i => acc.map (· * pe.1 ^ i)

end Impl

/-- Every divisor of `n`, in increasing order. `0` is given none, since every
number divides it. -/
def divisors (n : Nat) : Array Nat :=
  if n = 0 then #[]
  else ((((factorize n).toList.foldl Impl.divisorStep [1])).mergeSort (· ≤ ·)).toArray

end NumberTheory

end Cplib
