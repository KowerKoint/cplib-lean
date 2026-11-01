import Cplib.Structure.SegTree.Basic
import Cplib.Util.Unwrap.Basic

namespace Cplib

/-!
# Structure.LazySegTree.Basic

A segment tree with lazy propagation: range products over `M`, plus range
application of actions drawn from `F`.

Five functions make the tree, and they live in its type, so nothing has to be
wrapped to reach them:

- `op : M → M → M` with identity `e : M`, the product over values;
- `comp : F → F → F` with identity `noop : F`, composition of actions;
- `act : F → M → M`, how an action changes a value.

They are expected to satisfy, and nothing enforces it:

- `op` associative with `e` its identity, and likewise `comp` with `noop`;
- `act (comp f g) x = act f (act g x)` and `act noop x = x`, so that stacked
  pending actions compose correctly;
- `act f (op x y) = op (act f x) (act f y)` and `act f e = e`, so that an action
  applied to a whole subtree agrees with applying it to each leaf.

Violating them yields unspecified results rather than an error.

Ranges are **half-open**, exactly as in `SegTree`: `prod l r` and
`applyRange l r f` cover `[l, r)`, bounds accept `sz`, and position-like
arguments accept up to `sz - 1`.

Costs, for a tree of `sz` elements: `allProd` is `O(1)`, `ofArray` is `O(sz)`,
and `prod`, `get`, `apply`, `applyRange`, `maxRight` and `minLeft` are
`O(log sz)`. Note that `get` is `O(log sz)` here, unlike `SegTree.get`, because
pending actions on the path have to be resolved.

Range-add with range-sum is the standard example. A value carries a running
sum alongside the length it covers, so that an action knows how many elements
it is spread over, and an action is the amount being added:

```lean
let t := LazySegTree.ofArray
  (fun x y => (x.1 + y.1, x.2 + y.2)) ((0, 0) : Nat × Nat)
  (· + ·) (0 : Nat)
  (fun f x => (x.1 + f * x.2, x.2))
  (#[1, 2, 3, 4, 5].map fun v => (v, 1))
let t := t.applyRange! 1 4 10   -- add 10 to positions 1, 2, 3
(t.prod! 0 5).1                 -- 45, that is 15 + 3 * 10
```

Every function that uses one of the five is `@[specialize]`, so a tree built
with known operations calls them directly rather than through closures.
-/

structure LazySegTree (M F : Type) (op : M → M → M) (e : M)
    (comp : F → F → F) (noop : F) (act : F → M → M) where
  sz : Nat
  cap : Nat
  sz_le : sz ≤ cap
  cap_pos : 0 < cap
  cap_pow2 : cap.isPowerOfTwo
  data : Vector M (cap * 2)
  lazy : Vector F (cap * 2)

namespace LazySegTree
variable {M F : Type} {op : M → M → M} {e : M} {comp : F → F → F} {noop : F} {act : F → M → M}

namespace Impl

def setD {n : Nat} (xs : Vector α n) (i : Nat) (x : α) : Vector α n :=
  if h : i < n then xs.set i x else xs

@[specialize] def applyNode (e : M) (comp : F → F → F) (noop : F) (act : F → M → M)
    {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) (f : F) : Vector M (cap * 2) × Vector F (cap * 2) :=
  (setD data i (act f (data.getD i e)), setD lazy i (comp f (lazy.getD i noop)))

/-- Push `i`'s pending action down to its two children.

Every value is read out before the first write. Nesting the writes instead, as
`setD (setD data left …) right (act f (data.getD right e))`, leaves the original
vector live for the outer argument while the inner write runs, so the write
finds it shared and copies the whole vector. -/
@[specialize] def push (e : M) (comp : F → F → F) (noop : F) (act : F → M → M)
    {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) : Vector M (cap * 2) × Vector F (cap * 2) :=
  let f := lazy.getD i noop
  let left := i * 2
  let right := left + 1
  let dataLeft := act f (data.getD left e)
  let dataRight := act f (data.getD right e)
  let lazyLeft := comp f (lazy.getD left noop)
  let lazyRight := comp f (lazy.getD right noop)
  let data := setD (setD data left dataLeft) right dataRight
  let lazy := setD (setD (setD lazy left lazyLeft) right lazyRight) i noop
  (data, lazy)

@[specialize] def applyRange (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) {cap : Nat} (f : F) (ql qr : Nat) : Nat → Nat → Nat → Nat →
    Vector M (cap * 2) → Vector F (cap * 2) →
    Vector M (cap * 2) × Vector F (cap * 2)
  | 0, _, _, _, data, lazy => (data, lazy)
  | fuel + 1, i, l, r, data, lazy =>
      if qr ≤ l || r ≤ ql then (data, lazy)
      else if ql ≤ l && r ≤ qr then applyNode e comp noop act data lazy i f
      else
        let (data, lazy) := push e comp noop act data lazy i
        let mid := l + (r - l) / 2
        let (data, lazy) := applyRange op e comp noop act f ql qr fuel (i * 2) l mid data lazy
        let (data, lazy) := applyRange op e comp noop act f ql qr fuel (i * 2 + 1) mid r data lazy
        (setD data i (op (data.getD (i * 2) e) (data.getD (i * 2 + 1) e)), lazy)

@[specialize] def prod (op : M → M → M) (e : M) (comp : F → F → F) (noop : F) (act : F → M → M)
    {cap : Nat} (ql qr : Nat) : Nat → Nat → Nat → Nat → F →
    Vector M (cap * 2) → Vector F (cap * 2) → M
  | 0, _, _, _, _, _, _ => e
  | fuel + 1, i, l, r, pending, data, lazy =>
      if qr ≤ l || r ≤ ql then e
      else if ql ≤ l && r ≤ qr then act pending (data.getD i e)
      else
        let mid := l + (r - l) / 2
        let pending := comp pending (lazy.getD i noop)
        op (prod op e comp noop act ql qr fuel (i * 2) l mid pending data lazy)
          (prod op e comp noop act ql qr fuel (i * 2 + 1) mid r pending data lazy)

@[specialize] def maxRight (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) {cap : Nat} (sz ql : Nat) (p : M → Bool) :
    Nat → Nat → Nat → Nat → F → M →
    Vector M (cap * 2) → Vector F (cap * 2) → Option Nat × M
  | 0, _, l, _, _, acc, _, _ => (some l, acc)
  | fuel + 1, i, l, r, pending, acc, data, lazy =>
      if r ≤ ql || sz ≤ l then (none, acc)
      else
        let next := op acc (act pending (data.getD i e))
        if ql ≤ l && r ≤ sz && p next then (none, next)
        else if l + 1 ≥ r then (some l, acc)
        else
          let mid := l + (r - l) / 2
          let pending := comp pending (lazy.getD i noop)
          match maxRight op e comp noop act sz ql p fuel (i * 2) l mid pending acc data lazy with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) =>
              maxRight op e comp noop act sz ql p fuel (i * 2 + 1) mid r pending acc data lazy

@[specialize] def minLeft (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) {cap : Nat} (sz qr : Nat) (p : M → Bool) :
    Nat → Nat → Nat → Nat → F → M →
    Vector M (cap * 2) → Vector F (cap * 2) → Option Nat × M
  | 0, _, _, r, _, acc, _, _ => (some r, acc)
  | fuel + 1, i, l, r, pending, acc, data, lazy =>
      if qr ≤ l || sz ≤ l then (none, acc)
      else
        let next := op (act pending (data.getD i e)) acc
        if r ≤ qr && r ≤ sz && p next then (none, next)
        else if l + 1 ≥ r then (some r, acc)
        else
          let mid := l + (r - l) / 2
          let pending := comp pending (lazy.getD i noop)
          match minLeft op e comp noop act sz qr p fuel (i * 2 + 1) mid r pending acc data lazy with
          | (some answer, acc) => (some answer, acc)
          | (none, acc) =>
              minLeft op e comp noop act sz qr p fuel (i * 2) l mid pending acc data lazy

end Impl

/-- Build a tree whose position `i` holds `xs[i]`, with no pending action.
`O(xs.size)`. -/
@[specialize] def ofArray (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) (xs : Array M) : LazySegTree M F op e comp noop act :=
  let tree := SegTree.ofArray op e xs
  { tree with lazy := Vector.replicate (tree.cap * 2) noop }

/-- A tree of `n` copies of `e`. `O(n)`. -/
@[specialize] def replicate (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) (n : Nat) : LazySegTree M F op e comp noop act :=
  ofArray op e comp noop act (Array.replicate n e)

/-- Apply `f` to every position in the half-open range `[l, r)`. Both bounds may
be `sz`, and `r ≤ l` is a no-op. `O(log sz)`. -/
@[specialize] def applyRange (self : LazySegTree M F op e comp noop act)
    (l r : Fin (self.sz + 1)) (f : F) : LazySegTree M F op e comp noop act :=
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
  let (data, lazy) := Impl.applyRange op e comp noop act f ql qr cap 1 0 cap data lazy
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, data, lazy⟩

/-- Product over the half-open range `[l, r)`, left to right, with pending
actions resolved. `r ≤ l` gives `e`. `O(log sz)`. -/
@[specialize] def prod (self : LazySegTree M F op e comp noop act)
    (l r : Fin (self.sz + 1)) : M :=
  Impl.prod op e comp noop act l r self.cap 1 0 self.cap noop self.data self.lazy

/-- The value at position `i`, with pending actions resolved. `O(log sz)`. -/
@[specialize] def get (self : LazySegTree M F op e comp noop act) (i : Fin self.sz) : M :=
  self.prod ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- Apply `f` to position `i` alone. `O(log sz)`. -/
@[specialize] def apply (self : LazySegTree M F op e comp noop act) (i : Fin self.sz) (f : F) :
    LazySegTree M F op e comp noop act :=
  self.applyRange ⟨i, by omega⟩ ⟨i + 1, by omega⟩ f

/-- Product of the entire array, that is `prod 0 sz`. `O(1)`. -/
def allProd (self : LazySegTree M F op e comp noop act) : M := self.data.getD 1 e

/-- The largest `r ≥ l` with `p (prod l r) = true`, or `l` itself when even the
empty product fails `p`.

Meaningful when `p` is downward closed along `r` and `p e = true`, and then
`O(log sz)`; see `SegTree.maxRight`. -/
@[specialize] def maxRight (self : LazySegTree M F op e comp noop act)
    (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.maxRight op e comp noop act self.sz l p self.cap 1 0 self.cap noop e
    self.data self.lazy).1.getD self.sz

/-- The smallest `l ≤ r` with `p (prod l r) = true`, or `r` itself when even the
empty product fails `p`. The mirror image of `maxRight`; `O(log sz)` under the
same assumptions. -/
@[specialize] def minLeft (self : LazySegTree M F op e comp noop act)
    (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.minLeft op e comp noop act self.sz r p self.cap 1 0 self.cap noop e
    self.data self.lazy).1.getD 0

/-- `applyRange` for `Nat` bounds: `none` unless both `l ≤ sz` and `r ≤ sz`. -/
@[specialize] def applyRange? (self : LazySegTree M F op e comp noop act) (l r : Nat) (f : F) :
    Option (LazySegTree M F op e comp noop act) :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    some (self.applyRange ⟨l, h.1⟩ ⟨r, h.2⟩ f)
  else none

/-- `applyRange` for `Nat` bounds, reporting a panic unless both `l ≤ sz` and `r ≤ sz` and then
returning the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def applyRange! (self : LazySegTree M F op e comp noop act) (l r : Nat) (f : F) :
    LazySegTree M F op e comp noop act :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    self.applyRange ⟨l, h.1⟩ ⟨r, h.2⟩ f
  else outOfBounds! "LazySegTree.applyRange!" self

/-- `prod` for `Nat` bounds: `none` unless both `l ≤ sz` and `r ≤ sz`. -/
@[specialize] def prod? (self : LazySegTree M F op e comp noop act) (l r : Nat) : Option M :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    some (self.prod ⟨l, h.1⟩ ⟨r, h.2⟩)
  else none

/-- `prod` for `Nat` bounds, reporting a panic unless both `l ≤ sz` and `r ≤ sz` and then
returning `e`. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def prod! (self : LazySegTree M F op e comp noop act) (l r : Nat) : M :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then self.prod ⟨l, h.1⟩ ⟨r, h.2⟩
  else outOfBounds! "LazySegTree.prod!" e

/-- `get` for `Nat` bounds: `none` unless `i < sz`. -/
@[specialize] def get? (self : LazySegTree M F op e comp noop act) (i : Nat) : Option M :=
  if h : i < self.sz then some (self.get ⟨i, h⟩) else none

/-- `get` for `Nat` bounds, reporting a panic unless `i < sz` and then
returning `e`. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def get! (self : LazySegTree M F op e comp noop act) (i : Nat) : M :=
  if h : i < self.sz then self.get ⟨i, h⟩
  else outOfBounds! "LazySegTree.get!" e

/-- `apply` for `Nat` bounds: `none` unless `i < sz`. -/
@[specialize] def apply? (self : LazySegTree M F op e comp noop act) (i : Nat) (f : F) :
    Option (LazySegTree M F op e comp noop act) :=
  if h : i < self.sz then some (self.apply ⟨i, h⟩ f) else none

/-- `apply` for `Nat` bounds, reporting a panic unless `i < sz` and then
returning the tree unchanged. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def apply! (self : LazySegTree M F op e comp noop act) (i : Nat) (f : F) :
    LazySegTree M F op e comp noop act :=
  if h : i < self.sz then self.apply ⟨i, h⟩ f
  else outOfBounds! "LazySegTree.apply!" self

/-- `maxRight` for `Nat` bounds: `none` unless `l ≤ sz`. -/
@[specialize] def maxRight? (self : LazySegTree M F op e comp noop act) (l : Nat)
    (p : M → Bool) : Option Nat :=
  if h : l < self.sz + 1 then some (self.maxRight ⟨l, h⟩ p) else none

/-- `maxRight` for `Nat` bounds, reporting a panic unless `l ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def maxRight! (self : LazySegTree M F op e comp noop act) (l : Nat)
    (p : M → Bool) : Nat :=
  unwrap! "LazySegTree.maxRight!" (self.maxRight? l p)

/-- `minLeft` for `Nat` bounds: `none` unless `r ≤ sz`. -/
@[specialize] def minLeft? (self : LazySegTree M F op e comp noop act) (r : Nat)
    (p : M → Bool) : Option Nat :=
  if h : r < self.sz + 1 then some (self.minLeft ⟨r, h⟩ p) else none

/-- `minLeft` for `Nat` bounds, reporting a panic unless `r ≤ sz` and then
returning `0`. See `Cplib.unwrap!`: a panic does not stop the program. -/
@[specialize] def minLeft! (self : LazySegTree M F op e comp noop act) (r : Nat)
    (p : M → Bool) : Nat :=
  unwrap! "LazySegTree.minLeft!" (self.minLeft? r p)

end LazySegTree

end Cplib
