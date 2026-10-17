import Cplib.Structure.LazySegTree.Basic
import Cplib.Structure.SegTree.Lemmas
import Mathlib.Tactic

namespace LazySegTree
variable {M F : Type}

@[simp] private theorem Impl.getD_setD_self {α : Type} {n i : Nat}
    (xs : Vector α n) (x default : α) (hi : i < n) :
    (Impl.setD xs i x).getD i default = x := by
  simp [Impl.setD, hi, Vector.getD, Array.getD]

@[simp] private theorem Impl.getD_setD_of_ne {α : Type} {n i j : Nat}
    (xs : Vector α n) (x default : α) (hij : i ≠ j) :
    (Impl.setD xs i x).getD j default = xs.getD j default := by
  unfold Impl.setD
  split
  · rename_i hi
    by_cases hj : j < n
    · unfold Vector.getD Array.getD
      simp only [Vector.size_toArray, hj, dite_true]
      exact Vector.getElem_set_ne hi hj hij
    · unfold Vector.getD Array.getD
      simp [hj]
  · rfl

private def internalAt [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) : Prop :=
  data.getD i 1 = lazy.getD i 1 •
    (data.getD (i * 2) 1 * data.getD (i * 2 + 1) 1)

private theorem Impl.applyNode_internalAt [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (hi0 : i ≠ 0) (hi : i < cap) (hvalid : internalAt data lazy i) :
    let result := Impl.applyNode data lazy i f
    internalAt result.1 result.2 i := by
  simp only [Impl.applyNode]
  unfold internalAt
  rw [Impl.getD_setD_self _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega : i ≠ i * 2),
    Impl.getD_setD_of_ne _ _ _ (by omega : i ≠ i * 2 + 1)]
  rw [mul_smul, hvalid, MulDistribMulAction.smul_mul]

private theorem Impl.applyNode_internalAt_of_away [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (hji : j ≠ i) (hleft : j * 2 ≠ i) (hright : j * 2 + 1 ≠ i)
    (hvalid : internalAt data lazy j) :
    let result := Impl.applyNode data lazy i f
    internalAt result.1 result.2 j := by
  simp only [Impl.applyNode]
  unfold internalAt
  rw [Impl.getD_setD_of_ne _ _ _ hji.symm,
    Impl.getD_setD_of_ne _ _ _ hji.symm,
    Impl.getD_setD_of_ne _ _ _ hleft.symm,
    Impl.getD_setD_of_ne _ _ _ hright.symm]
  exact hvalid

@[simp] theorem ofArray_sz [Mul M] [One M] [One F] (xs : Array M) :
    (ofArray (F := F) xs).sz = xs.size := rfl

@[simp] theorem applyRange_sz [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).sz = self.sz := rfl

@[simp] theorem applyRange_cap [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap = self.cap := rfl

@[simp] theorem applyRange_sz_le [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).sz_le = self.sz_le := rfl

@[simp] theorem applyRange_cap_pos [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap_pos = self.cap_pos := rfl

@[simp] theorem applyRange_cap_pow2 [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap_pow2 = self.cap_pow2 := rfl

/-- The representation invariant of a lazy segment tree.  An internal node stores
the action recorded at that node applied to the product of its children; unused
leaves contain the monoid identity. -/
def Valid [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (self : LazySegTree M F) : Prop :=
  (∀ i : Fin self.cap, i.val ≠ 0 →
    self.data[i.val]'(by
      have hi := i.isLt
      have hc := self.cap_pos
      omega) =
      self.lazy[i.val]'(by
        have hi := i.isLt
        have hc := self.cap_pos
        omega) •
        (self.data[i.val * 2]'(by
          have hi := i.isLt
          omega) *
        self.data[i.val * 2 + 1]'(by
          have hi := i.isLt
          omega))) ∧
  (∀ i : Fin self.cap, self.sz ≤ i.val →
    self.data[self.cap + i.val]'(by
      have hi := i.isLt
      omega) = 1)

theorem Valid.internalAt [Monoid M] [Monoid F] [MulDistribMulAction F M]
    {self : LazySegTree M F} (hself : self.Valid)
    (i : Nat) (hi0 : i ≠ 0) (hi : i < self.cap) :
    internalAt self.data self.lazy i := by
  have h := hself.1 ⟨i, hi⟩ hi0
  unfold LazySegTree.internalAt Vector.getD Array.getD
  simp only [Vector.size_toArray]
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega),
    dif_pos (by omega)]
  exact h

theorem Valid.padding [Monoid M] [Monoid F] [MulDistribMulAction F M]
    {self : LazySegTree M F} (hself : self.Valid)
    (i : Nat) (hsi : self.sz ≤ i) (hi : i < self.cap) :
    self.data.getD (self.cap + i) 1 = 1 := by
  have h := hself.2 ⟨i, hi⟩ hsi
  unfold Vector.getD Array.getD
  simp only [Vector.size_toArray]
  rw [dif_pos (by omega)]
  exact h

theorem ofArray_Valid [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (xs : Array M) : Valid (ofArray (F := F) xs) := by
  have h := SegTree.ofArray_Valid xs
  constructor
  · intro i hi0
    simpa [ofArray, Valid] using h.1 i hi0
  · intro i hi
    simpa [ofArray, Valid] using h.2 i hi

@[simp] theorem ofArray_lazy [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (xs : Array M) :
    (ofArray (F := F) xs).lazy =
      Vector.replicate (xs.size.nextPowerOfTwo * 2) 1 := rfl

@[simp] theorem allProd_ofArray [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (xs : Array M) :
    (ofArray (F := F) xs).allProd = (SegTree.ofArray xs).allProd := rfl

theorem apply_eq_applyRange [Mul M] [One M] [Mul F] [One F] [SMul F M]
    (self : LazySegTree M F) (i : Fin self.sz) (f : F) :
    self.apply i f = self.applyRange ⟨i, by omega⟩ ⟨i + 1, by omega⟩ f := rfl

private theorem Impl.prod_of_ge [Monoid M] [Monoid F] [MulDistribMulAction F M]
    {cap : Nat} (ql qr : Nat) (hqr : qr ≤ ql) (fuel i left right : Nat)
    (pending : F) (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) :
    Impl.prod ql qr fuel i left right pending data lazy = 1 := by
  induction fuel generalizing i left right pending with
  | zero => rfl
  | succ fuel ih =>
    simp only [Impl.prod]
    split
    · rfl
    · rename_i hdisjoint
      split
      · rename_i hfull
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          not_or] at hdisjoint hfull
        omega
      · rw [ih, ih, mul_one]

@[simp] theorem prod_of_ge [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (self : LazySegTree M F) (l r : Fin (self.sz + 1)) (h : r ≤ l) :
    self.prod l r = 1 := by
  exact Impl.prod_of_ge l r (by omega) self.cap 1 0 self.cap 1 self.data self.lazy

@[simp] theorem prod_self [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (self : LazySegTree M F) (i : Fin (self.sz + 1)) : self.prod i i = 1 :=
  prod_of_ge self i i (by rfl)

private structure SumLen where
  sum : Nat
  len : Nat
deriving BEq

private instance : Mul SumLen := ⟨fun x y => ⟨x.sum + y.sum, x.len + y.len⟩⟩
private instance : One SumLen := ⟨⟨0, 0⟩⟩

private structure AddTag where
  value : Nat
deriving BEq

private instance : Mul AddTag := ⟨fun f g => ⟨f.value + g.value⟩⟩
private instance : One AddTag := ⟨⟨0⟩⟩
private instance : SMul AddTag SumLen :=
  ⟨fun f x => ⟨x.sum + f.value * x.len, x.len⟩⟩

/-- 区間加算・区間和で、作用の合成順、重なる更新、部分区間問い合わせを確認する。 -/
example :
    let xs : Array SumLen := #[⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩, ⟨5, 1⟩]
    let tree : LazySegTree SumLen AddTag := ofArray xs
    let tree := tree.applyRange 1 4 ⟨10⟩
    let tree := tree.applyRange 2 5 ⟨3⟩
    tree.prod 0 5 == ⟨54, 5⟩ && tree.prod 2 4 == ⟨33, 2⟩ &&
      tree.get ⟨2, by decide⟩ == ⟨16, 1⟩ && tree.allProd == ⟨54, 5⟩ &&
      tree.maxRight 0 (fun x => x.sum ≤ 30) == 3 &&
      tree.minLeft 5 (fun x => x.sum ≤ 30) == 3 &&
      tree.maxRight 1 (fun x => x.sum ≤ 28) == 3 &&
      tree.minLeft 4 (fun x => x.sum ≤ 33) == 2 := by
  native_decide

end LazySegTree
