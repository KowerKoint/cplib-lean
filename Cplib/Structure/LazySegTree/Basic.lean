import Cplib.Structure.SegTree.Basic

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
  let (data, lazy) := applyNode data lazy (i * 2) f
  let (data, lazy) := applyNode data lazy (i * 2 + 1) f
  (data, setD lazy i 1)

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

/-- Largest `r` such that `p (prod l r)` remains true. Runs in `O(log² n)`. -/
def maxRight (self : LazySegTree M F) (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  bisectMaxBelow (self.sz + 1) fun r =>
    if r.val ≤ l.val then true else p (self.prod l r)

/-- Smallest `l` such that `p (prod l r)` is true. Runs in `O(log² n)`. -/
def minLeft (self : LazySegTree M F) (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  bisectMinBelow (r.val + 1) fun l =>
    if h : l.val < self.sz + 1 then p (self.prod ⟨l, h⟩ r) else true

end LazySegTree
