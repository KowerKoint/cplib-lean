import Cplib.Util.List.Basic
import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# NumberTheory.Sieve.Basic

A sieve of Eratosthenes that remembers, for every number it covers, the least
prime that divides it.

`Sieve.build n` costs `O(n log log n)` and `O(n)` memory. What it keeps is
worth more than a table of flags: with the least prime factor of every number
in hand, `isPrime` is a comparison, and `factorize` divides the number down one
recorded factor at a time, in `O(log i)` rather than `O(√i)`.

```lean
let s := Sieve.build 1000000
s.isPrime! 999983          -- true
s.primes.size              -- 78498
s.factorize! 999999        -- #[(3, 3), (7, 1), (11, 1), (13, 1), (37, 1)]
s.primeFactors! 360        -- #[2, 2, 2, 3, 3, 5]
```

For a single number too large to sieve for, reach for `NumberTheory.isPrime`
and `NumberTheory.factorize` instead.
-/

namespace NumberTheory

/-- The numbers `0 … n`, each with its least prime factor. -/
structure Sieve (n : Nat) where
  /-- `minFactor[i]` is the least prime factor of `i` when `2 ≤ i`, and `0` for
  `i` below `2`. -/
  minFactor : Vector Nat (n + 1)
  /-- The primes up to `n`, in increasing order. -/
  primes : Array Nat

namespace Sieve
namespace Impl

/-- Write `i` at `j, j + i, j + 2i, …` wherever nothing is written yet. -/
def markFrom (n i : Nat) (hi : 0 < i) (spf : Vector Nat (n + 1)) (j : Nat) :
    Vector Nat (n + 1) :=
  if h : j ≤ n then
    let spf := if spf[j]'(by omega) == 0 then spf.set j i (by omega) else spf
    markFrom n i hi spf (j + i)
  else spf
termination_by n + 1 - j
decreasing_by omega

/-- Sieve the numbers from `i` up.

Nothing written at `i` means no smaller number divides it, so `i` is prime: it
records itself, joins the list, and marks its own multiples from `i * i`, every
smaller multiple already carrying a smaller factor. -/
def sieveFrom (n : Nat) (spf : Vector Nat (n + 1)) (primes : Array Nat) (i : Nat) :
    Vector Nat (n + 1) × Array Nat :=
  if h : i ≤ n then
    if h2 : 2 ≤ i ∧ spf[i]'(by omega) == 0 then
      let spf := spf.set i i (by omega)
      let spf := markFrom n i (by omega) spf (i * i)
      sieveFrom n spf (primes.push i) (i + 1)
    else sieveFrom n spf primes (i + 1)
  else (spf, primes)
termination_by n + 1 - i
decreasing_by all_goals omega

end Impl

/-- Sieve `0 … n`. `O(n log log n)`. -/
def build (n : Nat) : Sieve n :=
  let (minFactor, primes) := Impl.sieveFrom n (Vector.replicate (n + 1) 0) #[] 2
  ⟨minFactor, primes⟩

/-- The least prime factor of `i`, or `0` when `i` is below `2`. `O(1)`. -/
def minFac (self : Sieve n) (i : Fin (n + 1)) : Nat := self.minFactor[i]

/-- Whether `i` is prime. `O(1)`. -/
def isPrime (self : Sieve n) (i : Fin (n + 1)) : Bool := 2 ≤ i.val && self.minFactor[i] == i.val

namespace Impl

/-- Divide `i` down by the factor recorded for it, collecting the factors. -/
def factorsAux (self : Sieve n) (i : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
      if h : 2 ≤ i ∧ i < n + 1 then
        let p := self.minFactor[i]'h.2
        if p < 2 then [] else p :: factorsAux self (i / p) fuel
      else []

end Impl

/-- The prime factors of `i` with multiplicity, in increasing order.
`O(log i)`. -/
def primeFactors (self : Sieve n) (i : Fin (n + 1)) : Array Nat :=
  (Impl.factorsAux self i.val (i.val + 1)).toArray

/-- The prime factorisation of `i` as `(prime, exponent)` pairs, in increasing
order of prime. `O(log i)`. -/
def factorize (self : Sieve n) (i : Fin (n + 1)) : Array (Nat × Nat) :=
  (Impl.factorsAux self i.val (i.val + 1)).runLength.toArray

/-- `minFac` for a `Nat` index: `none` unless `i ≤ n`. -/
def minFac? (self : Sieve n) (i : Nat) : Option Nat :=
  if h : i < n + 1 then some (self.minFac ⟨i, h⟩) else none

/-- `minFac` for a `Nat` index, reporting a panic unless `i ≤ n` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def minFac! (self : Sieve n) (i : Nat) : Nat :=
  unwrap! "Sieve.minFac!" (self.minFac? i)

/-- `isPrime` for a `Nat` index: `none` unless `i ≤ n`. -/
def isPrime? (self : Sieve n) (i : Nat) : Option Bool :=
  if h : i < n + 1 then some (self.isPrime ⟨i, h⟩) else none

/-- `isPrime` for a `Nat` index, reporting a panic unless `i ≤ n` and then
returning `false`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def isPrime! (self : Sieve n) (i : Nat) : Bool :=
  unwrap! "Sieve.isPrime!" (self.isPrime? i)

/-- `primeFactors` for a `Nat` index: `none` unless `i ≤ n`. -/
def primeFactors? (self : Sieve n) (i : Nat) : Option (Array Nat) :=
  if h : i < n + 1 then some (self.primeFactors ⟨i, h⟩) else none

/-- `primeFactors` for a `Nat` index, reporting a panic unless `i ≤ n` and then
returning `#[]`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def primeFactors! (self : Sieve n) (i : Nat) : Array Nat :=
  unwrap! "Sieve.primeFactors!" (self.primeFactors? i)

/-- `factorize` for a `Nat` index: `none` unless `i ≤ n`. -/
def factorize? (self : Sieve n) (i : Nat) : Option (Array (Nat × Nat)) :=
  if h : i < n + 1 then some (self.factorize ⟨i, h⟩) else none

/-- `factorize` for a `Nat` index, reporting a panic unless `i ≤ n` and then
returning `#[]`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def factorize! (self : Sieve n) (i : Nat) : Array (Nat × Nat) :=
  unwrap! "Sieve.factorize!" (self.factorize? i)

end Sieve

end NumberTheory

end Cplib
