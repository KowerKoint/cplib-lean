import Cplib.Structure.SegTree.Basic
import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.LazySegTree.Basic

A segment tree with lazy propagation: range products over a monoid `M`, plus
range application of actions drawn from a monoid `F`.

`Mul M` must be associative with `One M` as its identity, and likewise for
`Mul F` and `One F`. The action `SMul F M` must be a monoid action that
distributes over the product:

- `(f * g) • x = f • (g • x)` and `(1 : F) • x = x`, so that stacked pending
  actions compose correctly;
- `f • (x * y) = (f • x) * (f • y)` and `f • (1 : M) = 1`, so that an action
  applied to a whole subtree agrees with applying it to each leaf.

Nothing enforces these; violating them yields unspecified results rather than
an error.

Ranges are **half-open**, exactly as in `SegTree`: `prod l r` and
`applyRange l r f` cover `[l, r)`, bounds accept `sz`, and position-like
arguments accept up to `sz - 1`.

Costs, for a tree of `sz` elements: `allProd` is `O(1)`, `ofArray` is `O(sz)`,
and `prod`, `get`, `apply`, `applyRange`, `maxRight` and `minLeft` are
`O(log sz)`. Note that `get` is `O(log sz)` here, unlike `SegTree.get`, because
pending actions on the path have to be resolved.

For range-add with range-sum, `M` carries a running sum alongside the length it
covers, so that an action knows how many elements it is spread over, and `F` is
the amount being added:

```lean
structure SumLen where
  sum : Nat
  len : Nat
instance : Mul SumLen := ⟨fun x y => ⟨x.sum + y.sum, x.len + y.len⟩⟩
instance : One SumLen := ⟨⟨0, 0⟩⟩

structure AddTag where
  value : Nat
instance : Mul AddTag := ⟨fun f g => ⟨f.value + g.value⟩⟩
instance : One AddTag := ⟨⟨0⟩⟩
instance : SMul AddTag SumLen := ⟨fun f x => ⟨x.sum + f.value * x.len, x.len⟩⟩

let t : LazySegTree SumLen AddTag :=
  LazySegTree.ofArray #[⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩]
let t := t.applyRange! 1 4 ⟨10⟩   -- add 10 to positions 1, 2, 3
t.prod! 0 5                        -- ⟨45, 5⟩, that is 15 + 3 * 10
```

`Cplib/Structure/LazySegTree/Lemmas.lean` exercises this instance further.
-/

structure LazySegTree (M F : Type) where
  sz : Nat
  cap : Nat
  sz_le : sz ≤ cap
  cap_pos : 0 < cap
  cap_pow2 : cap.isPowerOfTwo
  data : Vector M (cap * 2)
  lazy : Vector F (cap * 2)

namespace LazySegTree
variable {M F : Type} [Mul M] [One M] [Mul F] [One F] [SMul F M]

namespace Impl

def setD {n : Nat} (xs : Vector α n) (i : Nat) (x : α) : Vector α n :=
  if h : i < n then xs.set i x else xs

def applyNode {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) (f : F) : Vector M (cap * 2) × Vector F (cap * 2) :=
  (setD data i (f • data.getD i 1), setD lazy i (f * lazy.getD i 1))

/-- Push `i`'s pending action down to its two children.

Every value is read out before the first write. Nesting the writes instead, as
`setD (setD data left …) right (f • data.getD right 1)`, leaves the original
vector live for the outer argument while the inner write runs, so the write
finds it shared and copies the whole vector. -/
def push {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) : Vector M (cap * 2) × Vector F (cap * 2) :=
  let f := lazy.getD i 1
  let left := i * 2
  let right := left + 1
  let dataLeft := f • data.getD left 1
  let dataRight := f • data.getD right 1
  let lazyLeft := f * lazy.getD left 1
  let lazyRight := f * lazy.getD right 1
  let data := setD (setD data left dataLeft) right dataRight
  let lazy := setD (setD (setD lazy left lazyLeft) right lazyRight) i 1
  (data, lazy)

def applyRange {cap : Nat} (f : F) (ql qr : Nat) : Nat → Nat → Nat → Nat →
    Vector M (cap * 2) → Vector F (cap * 2) →
    Vector M (cap * 2) × Vector F (cap * 2)
  | 0, _, _, _, data, lazy => (data, lazy)
  | fuel + 1, i, l, r, data, lazy =>
      if qr ≤ l || r ≤ ql then (data, lazy)
      else if ql ≤ l && r ≤ qr then applyNode data lazy i f
      else
        let (data, lazy) := push data lazy i
        let mid := l + (r - l) / 2
        let (data, lazy) := applyRange f ql qr fuel (i * 2) l mid data lazy
        let (data, lazy) := applyRange f ql qr fuel (i * 2 + 1) mid r data lazy
        (setD data i (data.getD (i * 2) 1 * data.getD (i * 2 + 1) 1), lazy)

def prod {cap : Nat} (ql qr : Nat) : Nat → Nat → Nat → Nat → F →
    Vector M (cap * 2) → Vector F (cap * 2) → M
  | 0, _, _, _, _, _, _ => 1
  | fuel + 1, i, l, r, pending, data, lazy =>
      if qr ≤ l || r ≤ ql then 1
      else if ql ≤ l && r ≤ qr then pending • data.getD i 1
      else
        let mid := l + (r - l) / 2
        let pending := pending * lazy.getD i 1
        prod ql qr fuel (i * 2) l mid pending data lazy *
          prod ql qr fuel (i * 2 + 1) mid r pending data lazy

def maxRight {cap : Nat} (sz ql : Nat) (p : M → Bool) :
    Nat → Nat → Nat → Nat → F → M →
    Vector M (cap * 2) → Vector F (cap * 2) → Option Nat × M
  | 0, _, l, _, _, acc, _, _ => (some l, acc)
  | fuel + 1, i, l, r, pending, acc, data, lazy =>
      if r ≤ ql || sz ≤ l then (none, acc)
      else
        let next := acc * (pending • data.getD i 1)
        if ql ≤ l && r ≤ sz && p next then (none, next)
        else if l + 1 ≥ r then (some l, acc)
        else
          let mid := l + (r - l) / 2
          let pending := pending * lazy.getD i 1
          match maxRight sz ql p fuel (i * 2) l mid pending acc data lazy with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) =>
              maxRight sz ql p fuel (i * 2 + 1) mid r pending acc data lazy

def minLeft {cap : Nat} (sz qr : Nat) (p : M → Bool) :
    Nat → Nat → Nat → Nat → F → M →
    Vector M (cap * 2) → Vector F (cap * 2) → Option Nat × M
  | 0, _, _, r, _, acc, _, _ => (some r, acc)
  | fuel + 1, i, l, r, pending, acc, data, lazy =>
      if qr ≤ l || sz ≤ l then (none, acc)
      else
        let next := (pending • data.getD i 1) * acc
        if r ≤ qr && r ≤ sz && p next then (none, next)
        else if l + 1 ≥ r then (some r, acc)
        else
          let mid := l + (r - l) / 2
          let pending := pending * lazy.getD i 1
          match minLeft sz qr p fuel (i * 2 + 1) mid r pending acc data lazy with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) => minLeft sz qr p fuel (i * 2) l mid pending acc data lazy

end Impl

/-- Build a tree whose position `i` holds `xs[i]`, with no pending action.
`O(xs.size)`. -/
def ofArray (xs : Array M) : LazySegTree M F :=
  let tree := SegTree.ofArray xs
  { tree with lazy := Vector.replicate (tree.cap * 2) 1 }

/-- A tree of `n` copies of `One M`. `O(n)`. -/
def replicate (n : Nat) : LazySegTree M F := ofArray (Array.replicate n 1)

/-- Apply `f` to every position in the half-open range `[l, r)`. Both bounds may
be `sz`, and `r ≤ l` is a no-op. `O(log sz)`. -/
def applyRange (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    LazySegTree M F :=
  -- Every field comes out of the structure before `Impl.applyRange` runs. While
  -- the tree still holds `data` and `lazy`, each `Vector.set` inside finds them
  -- shared and copies, which costs `O(sz)` per call instead of `O(log sz)`.
  let ql := l.val
  let qr := r.val
  let sz := self.sz
  let cap := self.cap
  let sz_le := self.sz_le
  let cap_pos := self.cap_pos
  let cap_pow2 := self.cap_pow2
  let data := self.data
  let lazy := self.lazy
  let (data, lazy) := Impl.applyRange f ql qr cap 1 0 cap data lazy
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, data, lazy⟩

/-- Product over the half-open range `[l, r)`, left to right, with pending
actions resolved. `r ≤ l` gives `One M`. `O(log sz)`. -/
def prod (self : LazySegTree M F) (l r : Fin (self.sz + 1)) : M :=
  Impl.prod l r self.cap 1 0 self.cap 1 self.data self.lazy

/-- The value at position `i`, with pending actions resolved. `O(log sz)`. -/
def get (self : LazySegTree M F) (i : Fin self.sz) : M :=
  self.prod ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- Apply `f` to position `i` alone. `O(log sz)`. -/
def apply (self : LazySegTree M F) (i : Fin self.sz) (f : F) : LazySegTree M F :=
  self.applyRange ⟨i, by omega⟩ ⟨i + 1, by omega⟩ f

/-- Product of the entire array, that is `prod 0 sz`. `O(1)`. -/
def allProd (self : LazySegTree M F) : M := self.data.getD 1 1

/-- The largest `r ≥ l` with `p (prod l r) = true`, or `l` itself when even the
empty product fails `p`.

Meaningful when `p` is downward closed along `r` and `p 1 = true`, and then
`O(log sz)`; see `SegTree.maxRight`. -/
def maxRight (self : LazySegTree M F) (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.maxRight self.sz l p self.cap 1 0 self.cap 1 1 self.data self.lazy).1.getD self.sz

/-- The smallest `l ≤ r` with `p (prod l r) = true`, or `r` itself when even the
empty product fails `p`. The mirror image of `maxRight`; `O(log sz)` under the
same assumptions. -/
def minLeft (self : LazySegTree M F) (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.minLeft self.sz r p self.cap 1 0 self.cap 1 1 self.data self.lazy).1.getD 0

/-- `applyRange` for `Nat` bounds: `none` unless both `l ≤ sz` and `r ≤ sz`. -/
def applyRange? (self : LazySegTree M F) (l r : Nat) (f : F) : Option (LazySegTree M F) :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    some (self.applyRange ⟨l, h.1⟩ ⟨r, h.2⟩ f)
  else none

/-- `applyRange` for `Nat` bounds, reporting a panic unless both `l ≤ sz` and `r ≤ sz` and then
returning the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program. -/
def applyRange! (self : LazySegTree M F) (l r : Nat) (f : F) : LazySegTree M F :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    self.applyRange ⟨l, h.1⟩ ⟨r, h.2⟩ f
  else outOfBounds! "LazySegTree.applyRange!" self

/-- `prod` for `Nat` bounds: `none` unless both `l ≤ sz` and `r ≤ sz`. -/
def prod? (self : LazySegTree M F) (l r : Nat) : Option M :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    some (self.prod ⟨l, h.1⟩ ⟨r, h.2⟩)
  else none

/-- `prod` for `Nat` bounds, reporting a panic unless both `l ≤ sz` and `r ≤ sz` and then
returning `One M`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def prod! (self : LazySegTree M F) (l r : Nat) : M :=
  let _ : Inhabited M := ⟨1⟩
  unwrap! "LazySegTree.prod!" (self.prod? l r)

/-- `get` for `Nat` bounds: `none` unless `i < sz`. -/
def get? (self : LazySegTree M F) (i : Nat) : Option M :=
  if h : i < self.sz then some (self.get ⟨i, h⟩) else none

/-- `get` for `Nat` bounds, reporting a panic unless `i < sz` and then
returning `One M`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def get! (self : LazySegTree M F) (i : Nat) : M :=
  let _ : Inhabited M := ⟨1⟩
  unwrap! "LazySegTree.get!" (self.get? i)

/-- `apply` for `Nat` bounds: `none` unless `i < sz`. -/
def apply? (self : LazySegTree M F) (i : Nat) (f : F) : Option (LazySegTree M F) :=
  if h : i < self.sz then some (self.apply ⟨i, h⟩ f) else none

/-- `apply` for `Nat` bounds, reporting a panic unless `i < sz` and then
returning the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program. -/
def apply! (self : LazySegTree M F) (i : Nat) (f : F) : LazySegTree M F :=
  if h : i < self.sz then self.apply ⟨i, h⟩ f
  else outOfBounds! "LazySegTree.apply!" self

/-- `maxRight` for `Nat` bounds: `none` unless `l ≤ sz`. -/
def maxRight? (self : LazySegTree M F) (l : Nat) (p : M → Bool) : Option Nat :=
  if h : l < self.sz + 1 then some (self.maxRight ⟨l, h⟩ p) else none

/-- `maxRight` for `Nat` bounds, reporting a panic unless `l ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def maxRight! (self : LazySegTree M F) (l : Nat) (p : M → Bool) : Nat :=
  unwrap! "LazySegTree.maxRight!" (self.maxRight? l p)

/-- `minLeft` for `Nat` bounds: `none` unless `r ≤ sz`. -/
def minLeft? (self : LazySegTree M F) (r : Nat) (p : M → Bool) : Option Nat :=
  if h : r < self.sz + 1 then some (self.minLeft ⟨r, h⟩ p) else none

/-- `minLeft` for `Nat` bounds, reporting a panic unless `r ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
def minLeft! (self : LazySegTree M F) (r : Nat) (p : M → Bool) : Nat :=
  unwrap! "LazySegTree.minLeft!" (self.minLeft? r p)

end LazySegTree

end Cplib
