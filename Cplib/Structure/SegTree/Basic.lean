import Cplib.Util.Number.Basic
import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.SegTree.Basic

A segment tree over a monoid, supporting point updates and range products.

`Mul M` must be associative with `One M` as its identity; `One M` is also what
the padding beyond `sz` holds and what out-of-range queries return, so it has to
be a genuine identity for the results to mean anything. The product is **not**
assumed commutative, and `prod l r` multiplies left to right.

Ranges are **half-open**: `prod l r` covers `[l, r)`, so `prod 0 sz` is the
total, also available as `allProd`. Range bounds accept `sz` itself, while
position-like arguments such as `get` and `set` accept up to `sz - 1`.

Costs, for a tree of `sz` elements: `get` and `allProd` are `O(1)`, `set` and
`prod` are `O(log sz)`, `ofArray` is `O(sz)`, and `maxRight` and `minLeft` are
`O(log sz)` when `p` is monotone (see their own documentation).

```lean
let t : SegTree Nat := SegTree.ofArray #[2, 3, 5, 7]   -- product monoid
t.prod! 1 3        -- 15, that is 3 * 5
t.allProd          -- 210
(t.set! 0 11).get! 0  -- 11
```
-/

structure SegTree (M : Type) where
  sz : Nat
  cap : Nat
  sz_le : sz ≤ cap
  cap_pos : 0 < cap
  cap_pow2 : cap.isPowerOfTwo
  data : Vector M (cap * 2)

namespace SegTree
variable {M : Type} [Mul M] [One M]

namespace Impl
def modifyUpData {cap : Nat} (data : Vector M (cap * 2)) (i : Fin cap) :
    Vector M (cap * 2) :=
  let data := data.set i <| data[↑i * 2] * data[↑i * 2 + 1]
  if i.val ≤ 1 then data
  else modifyUpData data ⟨i.val / 2, by
    omega
  ⟩

def modifyUp (self : SegTree M) (i : Fin self.cap) : SegTree M :=
  let sz := self.sz
  let cap := self.cap
  let sz_le := self.sz_le
  let cap_pos := self.cap_pos
  let cap_pow2 := self.cap_pow2
  let data := self.data
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, modifyUpData data i⟩

/-- Write `x` at the leaf `j` and refresh every ancestor.

This takes the vector, not the tree, and that is load-bearing: `Vector.set`
updates in place only while nothing else refers to the vector. Handed the tree,
it would still be holding `data` when the write happens, so every `set` would
copy the whole vector and the `O(log sz)` update would cost `O(sz)`. `set`
therefore projects every field out of the structure first. -/
def setData {cap : Nat} (data : Vector M (cap * 2)) (j : Nat) (hj : j < cap * 2) (x : M) :
    Vector M (cap * 2) :=
  let data := data.set j x hj
  if hroot : j ≤ 1 then data
  else modifyUpData data ⟨j / 2, by omega⟩

def prod (self : SegTree M) (i l r ql qr : Nat) : M :=
  if l ≥ r then 1
  else if l + 1 ≥ r then self.data.getD i 1
  else
    let m := l + (r - l) / 2
    if ql ≤ l ∧ r ≤ qr then self.data.getD i 1
    else if qr ≤ m then prod self (i * 2) l m ql qr
    else if m ≤ ql then prod self (i * 2 + 1) m r ql qr
    else prod self (i * 2) l m ql m * prod self (i * 2 + 1) m r m qr

/-- Search `[ql, sz)` from left to right, skipping every subtree whose product can
be appended to `acc` while preserving `p`. -/
def maxRight (self : SegTree M) (p : M → Bool) (ql : Nat) :
    Nat → Nat → Nat → Nat → M → Option Nat × M
  | 0, _, l, _, acc => (some l, acc)
  | fuel + 1, i, l, r, acc =>
      if r ≤ ql || self.sz ≤ l then (none, acc)
      else
        let next := acc * self.data.getD i 1
        if ql ≤ l && r ≤ self.sz && p next then (none, next)
        else if l + 1 ≥ r then (some l, acc)
        else
          let mid := l + (r - l) / 2
          match maxRight self p ql fuel (i * 2) l mid acc with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) => maxRight self p ql fuel (i * 2 + 1) mid r acc

/-- Search `[0, qr)` from right to left, skipping every subtree whose product can
be prepended to `acc` while preserving `p`. -/
def minLeft (self : SegTree M) (p : M → Bool) (qr : Nat) :
    Nat → Nat → Nat → Nat → M → Option Nat × M
  | 0, _, _, r, acc => (some r, acc)
  | fuel + 1, i, l, r, acc =>
      if qr ≤ l || self.sz ≤ l then (none, acc)
      else
        let next := self.data.getD i 1 * acc
        if r ≤ qr && r ≤ self.sz && p next then (none, next)
        else if l + 1 ≥ r then (some r, acc)
        else
          let mid := l + (r - l) / 2
          match minLeft self p qr fuel (i * 2 + 1) mid r acc with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) => minLeft self p qr fuel (i * 2) l mid acc
end Impl

/-- Build a tree whose position `i` holds `a[i]`. `O(a.size)`. -/
def ofArray (a : Array M) : SegTree M :=
  let sz := a.size
  let cap := sz.nextPowerOfTwo
  let sz_le : sz ≤ cap := by
    exact Nat.le_nextPowerOfTwo sz
  let cap_pow2 : Nat.isPowerOfTwo cap := Nat.isPowerOfTwo_nextPowerOfTwo sz
  let cap_pos : 0 < cap := Nat.pos_of_isPowerOfTwo cap_pow2
  let dataLeaf := Fin.foldl sz (fun dat i => dat.set (cap + i) a[i]) (Vector.replicate (cap*2) 1)
  let data := Fin.foldr cap (fun i dat => dat.set i (dat[i.val * 2] * dat[i.val * 2 + 1])) dataLeaf
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, data⟩

/-- A tree of `n` copies of `One M`. `O(n)`. -/
def replicate (n : Nat) : SegTree M :=
  ofArray <| Array.replicate n 1

/-- The value at position `i`. `O(1)`. -/
def get (self : SegTree M) (i : Fin self.sz) : M :=
  self.data[self.cap + i]'(by
    have hi := i.isLt
    have hs := self.sz_le
    omega)

/-- `get` for a `Nat` index: `none` unless `i < sz`. -/
def get? (self : SegTree M) (i : Nat) : Option M :=
  if hi : i < self.sz then some (get self ⟨i, hi⟩) else none

/-- `get` for a `Nat` index, reporting a panic unless `i < sz` and then returning
`One M`. See `Cplib.unwrap!`: a panic does not stop the program. `O(1)`. -/
def get! (self : SegTree M) (i : Nat) : M :=
  let _ : Inhabited M := ⟨1⟩
  unwrap! "SegTree.get!" (self.get? i)

/-- Replace the value at position `i` with `x`. `O(log sz)`.

The fields are taken apart before `Impl.setData` runs so that the vector it
writes to is not also held by this tree; see `Impl.setData`. -/
def set (self : SegTree M) (i : Fin self.sz) (x : M) : SegTree M :=
  let j := self.cap + i.val
  let hj : j < self.cap * 2 := by
    have hi := i.isLt
    have hs := self.sz_le
    omega
  let sz := self.sz
  let cap := self.cap
  let sz_le := self.sz_le
  let cap_pos := self.cap_pos
  let cap_pow2 := self.cap_pow2
  let data := self.data
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, Impl.setData data j hj x⟩

/-- `set` for a `Nat` index: `none` unless `i < sz`. -/
def set? (self : SegTree M) (i : Nat) (x : M) : Option (SegTree M) :=
  if hi : i < self.sz then some (self.set ⟨i, hi⟩ x) else none

/-- `set` for a `Nat` index, reporting a panic unless `i < sz` and then returning
the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program.

The range check is spelled out rather than delegated to `set?`, so that the
tree is not also held by an `Inhabited` default while `set` runs; see
`Cplib.outOfBounds!`. -/
def set! (self : SegTree M) (i : Nat) (x : M) : SegTree M :=
  if hi : i < self.sz then self.set ⟨i, hi⟩ x
  else outOfBounds! "SegTree.set!" self

/-- Product over the half-open range `[l, r)`, left to right. Both bounds may be
`sz`, and `r ≤ l` gives `One M`. `O(log sz)`. -/
def prod (self : SegTree M) (l r : Fin (self.sz + 1)) : M :=
  if l ≥ r then 1
  else Impl.prod self 1 0 self.cap l.val r.val

/-- `prod` for `Nat` bounds: `none` unless both `l ≤ sz` and `r ≤ sz`. -/
def prod? (self : SegTree M) (l r : Nat) : Option M :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    some (self.prod ⟨l, h.left⟩ ⟨r, h.right⟩)
  else none

/-- `prod` for `Nat` bounds, reporting a panic unless both `l ≤ sz` and `r ≤ sz`
and then returning `One M`. See `Cplib.unwrap!`: a panic does not stop the
program. -/
def prod! (self : SegTree M) (l r : Nat) : M :=
  let _ : Inhabited M := ⟨1⟩
  unwrap! "SegTree.prod!" (self.prod? l r)

/-- Product of the entire array, that is `prod 0 sz`. `O(1)`. -/
def allProd (self : SegTree M) : M := self.data.getD 1 1

/-- The largest `r ≥ l` with `p (prod l r) = true`, or `l` itself when even the
empty product fails `p`.

Meaningful when `p` is downward closed along `r`, that is, once `p` turns false
it stays false as the range grows, and `p 1 = true`. Under those assumptions it
runs in `O(log sz)`; for an arbitrary `p` the answer is some `r` the descent
happened to reach. -/
def maxRight (self : SegTree M) (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.maxRight self p l self.cap 1 0 self.cap 1).1.getD self.sz

/-- The smallest `l ≤ r` with `p (prod l r) = true`, or `r` itself when even the
empty product fails `p`.

The mirror image of `maxRight`: meaningful when `p` is downward closed as the
range grows leftwards and `p 1 = true`, and then `O(log sz)`. -/
def minLeft (self : SegTree M) (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.minLeft self p r self.cap 1 0 self.cap 1).1.getD 0

/-- `maxRight` for a `Nat` bound: `none` unless `l ≤ sz`. -/
def maxRight? (self : SegTree M) (l : Nat) (p : M → Bool) : Option Nat :=
  if h : l < self.sz + 1 then some (self.maxRight ⟨l, h⟩ p) else none

/-- `maxRight` for a `Nat` bound, reporting a panic unless `l ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def maxRight! (self : SegTree M) (l : Nat) (p : M → Bool) : Nat :=
  unwrap! "SegTree.maxRight!" (self.maxRight? l p)

/-- `minLeft` for a `Nat` bound: `none` unless `r ≤ sz`. -/
def minLeft? (self : SegTree M) (r : Nat) (p : M → Bool) : Option Nat :=
  if h : r < self.sz + 1 then some (self.minLeft ⟨r, h⟩ p) else none

/-- `minLeft` for a `Nat` bound, reporting a panic unless `r ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def minLeft! (self : SegTree M) (r : Nat) (p : M → Bool) : Nat :=
  unwrap! "SegTree.minLeft!" (self.minLeft? r p)
end SegTree

end Cplib
