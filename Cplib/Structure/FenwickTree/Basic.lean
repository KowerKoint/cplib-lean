import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.FenwickTree.Basic

A Fenwick tree (binary indexed tree) over a `Vector α n`, supporting point
updates and prefix queries.

All ranges are **half-open**: `prefixSum i` covers `[0, i)` and `sum l r`
covers `[l, r)`, so `prefixSum n` and `sum 0 n` are the total. Both accept `n`
itself, while position-like arguments such as `add` and `get` accept up to
`n - 1`.

`Add α` must be associative with `Zero α` as its identity. `sum` and `get`
additionally subtract one prefix from another, so they need `Sub α` to invert
addition, as in a group; on a type where subtraction truncates, such as `Nat`,
they are only meaningful while every prefix dominates the one before it.

Costs, for a tree of length `n`: `empty` is `O(n)`, `add`, `prefixSum`, `sum`
and `get` are `O(log n)`, and `ofArray` is `O(n log n)`.

```lean
let t := FenwickTree.ofArray #[3, 1, 4, 1, 5]
t.prefixSum! 4            -- 9,  the sum of [0, 4)
t.sum! 1 4                -- 6,  the sum of [1, 4)
(t.add! 2 10).get! 2      -- 14, the value at position 2 after adding 10
```
-/

/-- Array-backed Fenwick tree for prefix sums. -/
structure FenwickTree (α : Type) (n : Nat) where
  data : Vector α n

namespace FenwickTree
variable {α : Type} {n : Nat}

namespace Impl

def addFuel [Add α] (fuel : Nat) (data : Vector α n) (i : Nat) (x : α) : Vector α n :=
  match fuel with
  | 0 => data
  | fuel + 1 =>
      if hi : i < n then
        let data := data.set i (data[i] + x)
        addFuel fuel data (i ||| (i + 1)) x
      else data

def prefixFuel [Add α] [Zero α] (data : Vector α n) : Nat → Nat → α
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, i + 1 =>
      prefixFuel data fuel ((i + 1) &&& i) + data.getD i 0

end Impl

/-- An all-zero Fenwick tree of length `n`. `O(n)`. -/
def empty [Zero α] (n : Nat) : FenwickTree α n :=
  ⟨Vector.replicate n 0⟩

/-- Add `x` to position `i`. `O(log n)`. -/
def add [Add α] (self : FenwickTree α n) (i : Fin n) (x : α) : FenwickTree α n :=
  ⟨Impl.addFuel n self.data i x⟩

/-- Sum of the half-open prefix `[0, i)`. `i` may be `n`. `O(log n)`. -/
def prefixSum [Add α] [Zero α] (self : FenwickTree α n) (i : Fin (n + 1)) : α :=
  Impl.prefixFuel self.data n i

/-- Sum of the half-open interval `[l, r)`, computed as `prefixSum r - prefixSum l`.
Both bounds may be `n`, and `r < l` gives the negation of `sum r l`. `O(log n)`. -/
def sum [Add α] [Sub α] [Zero α] (self : FenwickTree α n)
    (l r : Fin (n + 1)) : α :=
  self.prefixSum r - self.prefixSum l

/-- The value at position `i`, recovered as `sum i (i + 1)`. `O(log n)`. -/
def get [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Fin n) : α :=
  self.sum ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- `add` for a `Nat` index: `none` unless `i < n`. -/
def add? [Add α] (self : FenwickTree α n) (i : Nat) (x : α) : Option (FenwickTree α n) :=
  if h : i < n then some (self.add ⟨i, h⟩ x) else none

/-- `add` for a `Nat` index, reporting a panic unless `i < n` and then returning
the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program. -/
def add! [Add α] (self : FenwickTree α n) (i : Nat) (x : α) : FenwickTree α n :=
  if h : i < n then self.add ⟨i, h⟩ x
  else outOfBounds! "FenwickTree.add!" self

/-- `prefixSum` for a `Nat` index: `none` unless `i ≤ n`. -/
def prefixSum? [Add α] [Zero α] (self : FenwickTree α n) (i : Nat) : Option α :=
  if h : i < n + 1 then some (self.prefixSum ⟨i, h⟩) else none

/-- `prefixSum` for a `Nat` index, reporting a panic unless `i ≤ n` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def prefixSum! [Add α] [Zero α] (self : FenwickTree α n) (i : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.prefixSum!" (self.prefixSum? i)

/-- `sum` for `Nat` bounds: `none` unless both `l ≤ n` and `r ≤ n`. -/
def sum? [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (l r : Nat) : Option α :=
  if h : l < n + 1 ∧ r < n + 1 then some (self.sum ⟨l, h.1⟩ ⟨r, h.2⟩) else none

/-- `sum` for `Nat` bounds, reporting a panic unless both `l ≤ n` and `r ≤ n` and
then returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def sum! [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (l r : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.sum!" (self.sum? l r)

/-- `get` for a `Nat` index: `none` unless `i < n`. -/
def get? [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Nat) : Option α :=
  if h : i < n then some (self.get ⟨i, h⟩) else none

/-- `get` for a `Nat` index, reporting a panic unless `i < n` and then returning
`0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def get! [Add α] [Sub α] [Zero α] (self : FenwickTree α n) (i : Nat) : α :=
  let _ : Inhabited α := ⟨0⟩
  unwrap! "FenwickTree.get!" (self.get? i)

/-- Build a Fenwick tree whose position `i` holds `xs[i]`. `O(n log n)`. -/
def ofArray [Add α] [Zero α] (xs : Array α) : FenwickTree α xs.size :=
  Fin.foldl xs.size (fun tree i => tree.add i xs[i]) (empty xs.size)

end FenwickTree

end Cplib
