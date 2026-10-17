import Cplib.Util.Number
import Cplib.Typical.Bisect.Basic

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
  { self with data := modifyUpData self.data i }

def setData (self : SegTree M) (i : Fin self.sz) (x : M) :
    Vector M (self.cap * 2) :=
  let j := self.cap + i.val
  let data := self.data.set j x (by
    have hi := i.isLt
    have hs := self.sz_le
    omega)
  if hroot : j ≤ 1 then data
  else modifyUpData data ⟨j / 2, by
    have hi := i.isLt
    have hs := self.sz_le
    omega⟩

def prod (self : SegTree M) (i l r ql qr : Nat) : M :=
  if l ≥ r then 1
  else if l + 1 ≥ r then self.data.getD i 1
  else
    let m := l + (r - l) / 2
    if ql ≤ l ∧ r ≤ qr then self.data.getD i 1
    else if qr ≤ m then prod self (i * 2) l m ql qr
    else if m ≤ ql then prod self (i * 2 + 1) m r ql qr
    else prod self (i * 2) l m ql m * prod self (i * 2 + 1) m r m qr
end Impl

def ofArray (a : Array M) : SegTree M :=
  let sz := a.size
  let cap := sz.nextPowerOfTwo
  let sz_le : sz ≤ cap := by
    exact Nat.le_nextPowerOfTwo sz
  let cap_pow2 : Nat.isPowerOfTwo cap := Nat.isPowerOfTwo_nextPowerOfTwo sz
  let cap_pos : 0 < cap := Nat.pos_of_isPowerOfTwo cap_pow2
  let dataLeaf := List.finRange sz |>.foldl (fun dat i => dat.set (cap + i) a[i]) (Vector.replicate (cap*2) 1)
  let data := List.finRange cap |>.foldr (fun i dat => dat.set i (dat[i.val * 2] * dat[i.val * 2 + 1])) dataLeaf
  ⟨sz, cap, sz_le, cap_pos, cap_pow2, data⟩

def replicate (n : Nat) : SegTree M :=
  ofArray <| Array.replicate n 1

def get (self : SegTree M) (i : Fin self.sz) : M :=
  self.data[self.cap + i]'(by
    have hi := i.isLt
    have hs := self.sz_le
    omega)

def get? (self : SegTree M) (i : Nat) : Option M :=
  if hi : i < self.sz then some (get self ⟨i, hi⟩) else none

def get! (self : SegTree M) (i : Nat) : M :=
  let _ : Inhabited M := ⟨1⟩
  self.get? i |>.get!

def set (self : SegTree M) (i : Fin self.sz) (x : M) : SegTree M :=
  { self with data := Impl.setData self i x }

def set! (self : SegTree M) (i : Nat) (x : M) : SegTree M :=
  if hi : i < self.sz then self.set ⟨i, hi⟩ x
  else self

def prod (self : SegTree M) (l r : Fin (self.sz + 1)) : M :=
  if l ≥ r then 1
  else Impl.prod self 1 0 self.cap l.val r.val

def prod! (self : SegTree M) (l r : Nat) : M :=
  if h : l < self.sz + 1 ∧ r < self.sz + 1 then
    self.prod ⟨l, h.left⟩ ⟨r, h.right⟩
  else
    1

/-- Product of the entire array. -/
def allProd (self : SegTree M) : M := self.data.getD 1 1

/-- Largest `r` such that `p (prod l r)` remains true. Runs in `O(log² n)`. -/
def maxRight (self : SegTree M) (l : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  bisectMaxBelow (self.sz + 1) fun r =>
    if r.val ≤ l.val then true else p (self.prod l r)

/-- Smallest `l` such that `p (prod l r)` is true. Runs in `O(log² n)`. -/
def minLeft (self : SegTree M) (r : Fin (self.sz + 1)) (p : M → Bool) : Nat :=
  bisectMinBelow (r.val + 1) fun l =>
    if h : l.val < self.sz + 1 then p (self.prod ⟨l, h⟩ r) else true
end SegTree
