import Cplib.Structure.SegTree.Basic

namespace Cplib

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

def push {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) : Vector M (cap * 2) × Vector F (cap * 2) :=
  let f := lazy.getD i 1
  let left := i * 2
  let right := left + 1
  let data := setD (setD data left (f • data.getD left 1))
    right (f • data.getD right 1)
  let lazy := setD (setD (setD lazy left (f * lazy.getD left 1))
    right (f * lazy.getD right 1)) i 1
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

def ofArray (xs : Array M) : LazySegTree M F :=
  let tree := SegTree.ofArray xs
  { tree with lazy := Vector.replicate (tree.cap * 2) 1 }

def replicate (n : Nat) : LazySegTree M F := ofArray (Array.replicate n 1)

def applyRange (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    LazySegTree M F :=
  let (data, lazy) := Impl.applyRange f l r self.cap 1 0 self.cap self.data self.lazy
  { self with data, lazy }

def prod (self : LazySegTree M F) (l r : Fin (self.sz + 1)) : M :=
  Impl.prod l r self.cap 1 0 self.cap 1 self.data self.lazy

/-- Value at one position. -/
def get (self : LazySegTree M F) (i : Fin self.sz) : M :=
  self.prod ⟨i, by omega⟩ ⟨i + 1, by omega⟩

/-- Apply an action to one position. -/
def apply (self : LazySegTree M F) (i : Fin self.sz) (f : F) : LazySegTree M F :=
  self.applyRange ⟨i, by omega⟩ ⟨i + 1, by omega⟩ f

/-- Product of the entire array. -/
def allProd (self : LazySegTree M F) : M := self.data.getD 1 1

/-- Largest `r` such that `p (prod l r)` remains true. Runs in `O(log n)` when
`p` is monotone and `p 1 = true`. -/
def maxRight (self : LazySegTree M F) (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.maxRight self.sz l p self.cap 1 0 self.cap 1 1 self.data self.lazy).1.getD self.sz

/-- Smallest `l` such that `p (prod l r)` is true. Runs in `O(log n)` when
`p` is monotone and `p 1 = true`. -/
def minLeft (self : LazySegTree M F) (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  (Impl.minLeft self.sz r p self.cap 1 0 self.cap 1 1 self.data self.lazy).1.getD 0

end LazySegTree

end Cplib
