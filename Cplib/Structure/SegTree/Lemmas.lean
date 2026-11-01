import Cplib.Structure.SegTree.Basic
import Cplib.Util.Vector.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.SegTree.Lemmas

Specification of the segment tree in `Structure.SegTree.Basic`.

`Valid` is the representation invariant: every internal node holds the product
of its two children, and the padding beyond `sz` holds `e`. `ofArray_Valid` and
`set_Valid` say that every state this API produces has it.

`prod_eq_range_prod` is what a range query means: under that invariant, and
with `op` associative with identity `e` — `Std.Associative` and
`Std.LawfulIdentity`, which the usual choices on `Nat` already carry — `prod l r`
is `op` folded over the elements of `[l, r)`.
-/

namespace SegTree
variable {M : Type} {op : M → M → M} {e : M}

/-- `op` folded over a list, which is what a range of the tree stands for. -/
private abbrev foldOp (op : M → M → M) (e : M) (l : List M) : M := l.foldr op e

private theorem foldOp_append [Std.Associative op] [Std.LawfulIdentity op e]
    (l₁ l₂ : List M) : foldOp op e (l₁ ++ l₂) = op (foldOp op e l₁) (foldOp op e l₂) := by
  induction l₁ with
  | nil => simp [foldOp, Std.LawfulLeftIdentity.left_id]
  | cons x l ih => simp [foldOp, ih, Std.Associative.assoc]

private def buildData (op : M → M → M) {cap : Nat} (xs : List (Fin cap))
    (data : Vector M (cap * 2)) : Vector M (cap * 2) :=
  xs.foldr (fun (i : Fin cap) dat =>
    dat.set i (op dat[i.val * 2] dat[i.val * 2 + 1])) data

private theorem buildData_valid {cap : Nat} (xs : List (Fin cap))
    (hxs : xs.Pairwise (· < ·)) (data : Vector M (cap * 2))
    (i : Fin cap) (hi : i ∈ xs) (hi0 : i.val ≠ 0) :
    (buildData op xs data)[i.val] =
      op (buildData op xs data)[i.val * 2] (buildData op xs data)[i.val * 2 + 1] := by
  induction xs with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [buildData, List.foldr_cons]
    simp only [List.pairwise_cons] at hxs
    simp only [List.mem_cons] at hi
    rcases hi with h | hi
    · subst i
      simp only [Vector.getElem_set_self]
      rw [Vector.getElem_set_ne, Vector.getElem_set_ne]
      all_goals omega
    · have hxi : x < i := hxs.1 i hi
      rw [Vector.getElem_set_ne, Vector.getElem_set_ne, Vector.getElem_set_ne]
      · exact ih hxs.2 hi
      all_goals omega

private theorem buildData_get_of_cap_le {cap : Nat} (xs : List (Fin cap))
    (data : Vector M (cap * 2)) (j : Nat) (hj : j < cap * 2) (hcap : cap ≤ j) :
    (buildData op xs data)[j] = data[j] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [buildData, List.foldr_cons]
    rw [Vector.getElem_set_ne]
    · exact ih
    · omega

@[simp] theorem ofArray_sz (op : M → M → M) (e : M) (a : Array M) :
    (ofArray op e a).sz = a.size := rfl

@[simp] theorem ofArray_cap (op : M → M → M) (e : M) (a : Array M) :
    (ofArray op e a).cap = a.size.nextPowerOfTwo := rfl

@[simp] theorem ofArray_get (op : M → M → M) (e : M) (a : Array M) (i : Fin a.size) :
    get (ofArray op e a) i = a[i] := by
  simp [get, ofArray, Fin.foldl_eq_finRange_foldl, Fin.foldr_eq_finRange_foldr]
  have hi := i.isLt
  have hs := Nat.le_nextPowerOfTwo a.size
  have hc : 0 < a.size.nextPowerOfTwo :=
    Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo a.size)
  let base : Vector M (a.size.nextPowerOfTwo * 2) :=
    Vector.replicate (a.size.nextPowerOfTwo * 2) e
  let leaves : Vector M (a.size.nextPowerOfTwo * 2) :=
    (List.finRange a.size).foldl
      (fun dat j => dat.set (a.size.nextPowerOfTwo + j.val) a[j.val] (by
        have hj := j.isLt
        omega)) base
  change (buildData op (List.finRange a.size.nextPowerOfTwo) leaves).get
    ⟨a.size.nextPowerOfTwo + i.val, by
      omega⟩ = a[i]
  calc
    _ = leaves[a.size.nextPowerOfTwo + i.val] :=
      buildData_get_of_cap_le _ _ _ (by
        omega) (by omega)
    _ = a[i] := by
      apply Vector.getElem_foldl_set_of_mem (List.finRange a.size)
        (fun j => a.size.nextPowerOfTwo + j.val)
        (fun j => by
          change a.size.nextPowerOfTwo + j.val < a.size.nextPowerOfTwo * 2
          have hj := j.isLt
          have hs := Nat.le_nextPowerOfTwo a.size
          have hc : 0 < a.size.nextPowerOfTwo :=
            Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo a.size)
          omega)
        (fun j => a[j.val]) base i (List.mem_finRange i) (List.nodup_finRange _)
      intro j hj hji
      apply Fin.ext
      omega

private theorem Impl.modifyUpData_get_of_cap_le {cap : Nat}
    (data : Vector M (cap * 2)) (i : Fin cap) (j : Nat)
    (hj : j < cap * 2) (hcap : cap ≤ j) :
    (Impl.modifyUpData op data i).get ⟨j, hj⟩ = data.get ⟨j, hj⟩ := by
  induction data, i using Impl.modifyUpData.induct (op := op) with
  | case1 data i hroot =>
    rw [Impl.modifyUpData.eq_def]
    simp only [if_pos hroot]
    change (data.set i _)[j] = data[j]
    rw [Vector.getElem_set_ne]
    omega
  | case2 data i data' hroot ih =>
    rw [Impl.modifyUpData.eq_def]
    simp only [if_neg hroot]
    rw [ih]
    change (data.set i _)[j] = data[j]
    rw [Vector.getElem_set_ne]
    omega

@[simp] theorem Impl.modifyUp_sz (self : SegTree M op e) (i : Fin self.cap) :
    (Impl.modifyUp self i).sz = self.sz := rfl

@[simp] theorem Impl.modifyUp_cap (self : SegTree M op e) (i : Fin self.cap) :
    (Impl.modifyUp self i).cap = self.cap := rfl

private theorem Impl.modifyUp_get_of_cap_le (self : SegTree M op e)
    (i : Fin self.cap) (j : Nat) (hj : j < self.cap * 2) (hcap : self.cap ≤ j) :
    (Impl.modifyUp self i).data[j] = self.data[j] := by
  exact Impl.modifyUpData_get_of_cap_le self.data i j hj hcap

/-- `Impl.setData` at the leaf `set` writes to, in the shape the proofs below
want: `set` itself has to spell the index out so that the structure is gone by
the time the vector is written. -/
private abbrev Impl.setDataAt (self : SegTree M op e) (i : Fin self.sz) (x : M) :
    Vector M (self.cap * 2) :=
  Impl.setData op self.data (self.cap + i.val) (by
    have hi := i.isLt
    have hs := self.sz_le
    omega) x

private theorem Impl.setData_get_self (self : SegTree M op e)
    (i : Fin self.sz) (x : M) :
    (Impl.setDataAt self i x).get ⟨self.cap + i.val, by
      have hi := i.isLt
      have hs := self.sz_le
      omega⟩ = x := by
  have hi := i.isLt
  have hs := self.sz_le
  have hc := self.cap_pos
  unfold Impl.setDataAt Impl.setData
  dsimp only
  split
  · change (self.data.set (self.cap + i.val) x _)[self.cap + i.val] = x
    rw [Vector.getElem_set_self]
  · rw [Impl.modifyUpData_get_of_cap_le _ _ _ (by omega) (by omega)]
    change (self.data.set (self.cap + i.val) x _)[self.cap + i.val] = x
    rw [Vector.getElem_set_self]

private theorem Impl.setData_get_of_ne (self : SegTree M op e)
    (i j : Fin self.sz) (x : M) (hij : j ≠ i) :
    (Impl.setDataAt self i x).get ⟨self.cap + j.val, by
      have hj := j.isLt
      have hs := self.sz_le
      omega⟩ = self.data.get ⟨self.cap + j.val, by
        have hj := j.isLt
        have hs := self.sz_le
        omega⟩ := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := self.sz_le
  have hc := self.cap_pos
  unfold Impl.setDataAt Impl.setData
  dsimp only
  split
  · change (self.data.set (self.cap + i.val) x _)[self.cap + j.val] =
      self.data[self.cap + j.val]
    rw [Vector.getElem_set_ne]
    omega
  · rw [Impl.modifyUpData_get_of_cap_le _ _ _ (by omega) (by omega)]
    change (self.data.set (self.cap + i.val) x _)[self.cap + j.val] =
      self.data[self.cap + j.val]
    rw [Vector.getElem_set_ne]
    omega

private def internalValidExcept (op : M → M → M) {cap : Nat} (data : Vector M (cap * 2))
    (bad : Fin cap) : Prop :=
  ∀ i : Fin cap, i.val ≠ 0 → i ≠ bad →
    data[i.val] = op data[i.val * 2] data[i.val * 2 + 1]

private def internalValid (op : M → M → M) {cap : Nat} (data : Vector M (cap * 2)) : Prop :=
  ∀ i : Fin cap, i.val ≠ 0 →
    data[i.val] = op data[i.val * 2] data[i.val * 2 + 1]

/-- Fold the perfect binary subtree of height `height` rooted at `i`, in leaf order. -/
private def nodeFold (op : M → M → M) (e : M) {cap : Nat} (data : Vector M (cap * 2))
    (i : Nat) : Nat → M
  | 0 => data.getD i e
  | height + 1 =>
      op (nodeFold op e data (i * 2) height) (nodeFold op e data (i * 2 + 1) height)

/-- From the local `internalValid` property, recover what the root of any perfect
binary subtree stands for. -/
private theorem nodeFold_eq_get {cap : Nat}
    (data : Vector M (cap * 2)) (hvalid : internalValid op data)
    (height i : Nat) (hi0 : i ≠ 0)
    (hibound : (i + 1) * 2 ^ height ≤ cap * 2) :
    nodeFold op e data i height = data.getD i e := by
  induction height generalizing i with
  | zero => rfl
  | succ height ih =>
    have hi : i < cap := by
      have hp : 2 ≤ 2 ^ (height + 1) := by
        rw [pow_succ]
        have := pow_pos (by omega : 0 < (2 : Nat)) height
        omega
      nlinarith
    have hleft : (i * 2 + 1) * 2 ^ height ≤ cap * 2 := by
      rw [pow_succ] at hibound
      nlinarith
    have hright : (i * 2 + 1 + 1) * 2 ^ height ≤ cap * 2 := by
      rw [pow_succ] at hibound
      nlinarith
    rw [nodeFold, ih (i := i * 2) (by omega) hleft,
      ih (i := i * 2 + 1) (by omega) hright]
    have hv := hvalid ⟨i, hi⟩ hi0
    simpa [Vector.getD, Array.getD, hi, show i < cap * 2 by omega,
      show i * 2 < cap * 2 by omega,
      show i * 2 + 1 < cap * 2 by omega] using hv.symm

private theorem nodeFold_eq_range_prod [Std.Associative op] [Std.LawfulIdentity op e]
    {cap : Nat} (data : Vector M (cap * 2)) (height i : Nat) :
    nodeFold op e data i height =
      foldOp op e ((List.range' (i * 2 ^ height) (2 ^ height)).map
        (fun j => data.getD j e)) := by
  induction height generalizing i with
  | zero => simp [nodeFold, foldOp, Std.LawfulRightIdentity.right_id]
  | succ height ih =>
    rw [nodeFold, ih (i := i * 2), ih (i := i * 2 + 1)]
    rw [← foldOp_append (op := op) (e := e), ← List.map_append]
    congr 2
    have hs : (i * 2 + 1) * 2 ^ height =
        i * 2 * 2 ^ height + 1 * 2 ^ height := by ring
    rw [hs]
    rw [List.range'_append]
    congr 1 <;> simp only [pow_succ] <;> ring

private def queryFold (op : M → M → M) (e : M) {cap : Nat} (data : Vector M (cap * 2))
    (i l ql qr : Nat) : Nat → M
  | 0 => data.getD i e
  | height + 1 =>
      let m := l + 2 ^ height
      if ql ≤ l ∧ l + 2 ^ (height + 1) ≤ qr then nodeFold op e data i (height + 1)
      else if qr ≤ m then queryFold op e data (i * 2) l ql qr height
      else if m ≤ ql then queryFold op e data (i * 2 + 1) m ql qr height
      else op (queryFold op e data (i * 2) l ql m height)
        (queryFold op e data (i * 2 + 1) m m qr height)

private theorem Impl.prod_eq_queryFold (self : SegTree M op e)
    (hvalid : internalValid op self.data) (height i l ql qr : Nat)
    (hi0 : i ≠ 0) (hibound : (i + 1) * 2 ^ height ≤ self.cap * 2) :
    Impl.prod self i l (l + 2 ^ height) ql qr =
      queryFold op e self.data i l ql qr height := by
  induction height generalizing i l ql qr with
  | zero => simp [Impl.prod, queryFold]
  | succ height ih =>
    have hp : 0 < 2 ^ height := pow_pos (by omega) _
    have hm : l + ((l + 2 ^ (height + 1)) - l) / 2 = l + 2 ^ height := by
      simp [pow_succ]
    have hleft : (i * 2 + 1) * 2 ^ height ≤ self.cap * 2 := by
      rw [pow_succ] at hibound
      nlinarith
    have hright : (i * 2 + 1 + 1) * 2 ^ height ≤ self.cap * 2 := by
      rw [pow_succ] at hibound
      nlinarith
    rw [Impl.prod.eq_def]
    simp only [show ¬ l ≥ l + 2 ^ (height + 1) by
      simp [pow_succ], if_false]
    simp only [show ¬ l + 1 ≥ l + 2 ^ (height + 1) by
      simp [pow_succ]; omega, if_false]
    rw [hm]
    unfold queryFold
    split
    · symm
      exact nodeFold_eq_get self.data hvalid (height + 1) i hi0 hibound
    · have hend : l + 2 ^ height * 2 =
          (l + 2 ^ height) + 2 ^ height := by omega
      rw [pow_succ, hend]
      simp_all

private theorem queryFold_eq_range_prod [Std.Associative op] [Std.LawfulIdentity op e]
    {cap : Nat} (data : Vector M (cap * 2)) (height i l ql qr : Nat)
    (hlq : l ≤ ql) (hqr : qr ≤ l + 2 ^ height) (hqq : ql < qr) :
    queryFold op e data i l ql qr height =
      foldOp op e ((List.range' (i * 2 ^ height + (ql - l)) (qr - ql)).map
        (fun j => data.getD j e)) := by
  induction height generalizing i l ql qr with
  | zero =>
    have : ql = l ∧ qr = l + 1 := by simp at hqr; omega
    rcases this with ⟨rfl, rfl⟩
    simp [queryFold, foldOp, Std.LawfulRightIdentity.right_id]
  | succ height ih =>
    have hp : 0 < 2 ^ height := pow_pos (by omega) _
    let m := l + 2 ^ height
    unfold queryFold
    split
    · rename_i hfull
      have hql : ql = l := by omega
      have hqr' : qr = l + 2 ^ (height + 1) := by omega
      subst ql; subst qr
      rw [nodeFold_eq_range_prod]
      (congr 2; simp [pow_succ])
    · rename_i hnfull
      dsimp only
      split
      · rename_i hleft
        rw [ih (i := i * 2) (l := l) (ql := ql) (qr := qr) hlq (by omega) hqq]
        apply congrArg (foldOp op e)
        apply congrArg (List.map (fun j => data.getD j e))
        rw [List.range'_inj]
        exact ⟨rfl, Or.inr (by simp [pow_succ]; ring)⟩
      · rename_i hnleft
        split
        · rename_i hright
          rw [ih (i := i * 2 + 1) (l := m) (ql := ql) (qr := qr)
            (by omega) (by simp [m, pow_succ] at hqr ⊢; omega) hqq]
          apply congrArg (foldOp op e)
          apply congrArg (List.map (fun j => data.getD j e))
          rw [List.range'_inj]
          refine ⟨rfl, Or.inr ?_⟩
          have hsub : ql - l = 2 ^ height + (ql - m) := by
            dsimp [m]
            omega
          rw [hsub]
          simp [m, pow_succ]
          ring
        · rename_i hnright
          rw [ih (i := i * 2) (l := l) (ql := ql) (qr := m)
                hlq (by omega) (by omega),
              ih (i := i * 2 + 1) (l := m) (ql := m) (qr := qr)
                (by omega) (by simp [m, pow_succ] at hqr ⊢; omega) (by omega)]
          rw [← foldOp_append (op := op) (e := e), ← List.map_append]
          congr 2
          have hs : (i * 2 + 1) * 2 ^ height + (m - m) =
              (i * 2 * 2 ^ height + (ql - l)) + (m - ql) := by
            have hparts : (ql - l) + (m - ql) = 2 ^ height := by
              dsimp [m]
              omega
            simp only [Nat.sub_self, add_zero]
            nlinarith
          rw [hs]
          rw [show List.range' (i * 2 * 2 ^ height + (ql - l)) (m - ql) ++
                List.range' (i * 2 * 2 ^ height + (ql - l) + (m - ql)) (qr - m) =
              List.range' (i * 2 * 2 ^ height + (ql - l))
                ((m - ql) + (qr - m)) by
            simpa only [one_mul] using (List.range'_append
              (s := i * 2 * 2 ^ height + (ql - l))
              (m := m - ql) (n := qr - m) (step := 1))]
          rw [List.range'_inj]
          constructor
          · omega
          · right
            simp [pow_succ]
            ring

private theorem repairNode_except_parent {cap : Nat}
    (data : Vector M (cap * 2)) (i : Fin cap) (hi : 1 < i.val)
    (hvalid : internalValidExcept op data i) :
    internalValidExcept op
      (data.set i (op data[i.val * 2] data[i.val * 2 + 1]))
      ⟨i.val / 2, by omega⟩ := by
  intro j hj0 hjp
  have hjpv : j.val ≠ i.val / 2 := by
    intro h
    apply hjp
    apply Fin.ext
    exact h
  by_cases hji : j = i
  · subst j
    rw [Vector.getElem_set_self]
    rw [Vector.getElem_set_ne, Vector.getElem_set_ne]
    all_goals omega
  · rw [Vector.getElem_set_ne, Vector.getElem_set_ne, Vector.getElem_set_ne]
    · exact hvalid j hj0 hji
    all_goals
      intro h
      apply hjp
      apply Fin.ext
      omega

private theorem repairNode_root {cap : Nat}
    (data : Vector M (cap * 2)) (i : Fin cap) (_hi0 : i.val ≠ 0) (hi : i.val ≤ 1)
    (hvalid : internalValidExcept op data i) :
    internalValid op (data.set i (op data[i.val * 2] data[i.val * 2 + 1])) := by
  intro j hj0
  by_cases hji : j = i
  · subst j
    rw [Vector.getElem_set_self]
    rw [Vector.getElem_set_ne, Vector.getElem_set_ne]
    all_goals omega
  · rw [Vector.getElem_set_ne, Vector.getElem_set_ne, Vector.getElem_set_ne]
    · exact hvalid j hj0 hji
    all_goals omega

private theorem Impl.modifyUpData_internalValid {cap : Nat}
    (data : Vector M (cap * 2)) (i : Fin cap) (hi0 : i.val ≠ 0)
    (hvalid : internalValidExcept op data i) :
    internalValid op (Impl.modifyUpData op data i) := by
  induction data, i using Impl.modifyUpData.induct (op := op) with
  | case1 data i hroot =>
    rw [Impl.modifyUpData.eq_def]
    simp only [if_pos hroot]
    exact repairNode_root data i hi0 hroot hvalid
  | case2 data i data' hroot ih =>
    rw [Impl.modifyUpData.eq_def]
    simp only [if_neg hroot]
    apply ih
    · change i.val / 2 ≠ 0
      omega
    · exact repairNode_except_parent data i (by omega) hvalid

@[simp] theorem set_sz (self : SegTree M op e)
    (i : Fin self.sz) (x : M) : (self.set i x).sz = self.sz := rfl

@[simp] theorem set_cap (self : SegTree M op e)
    (i : Fin self.sz) (x : M) : (self.set i x).cap = self.cap := rfl

@[simp] theorem get_set_self (self : SegTree M op e)
    (i : Fin self.sz) (x : M) : (self.set i x).get ⟨i, by simp⟩ = x := by
  exact Impl.setData_get_self self i x

@[simp] theorem get_set_of_ne (self : SegTree M op e)
    (i j : Fin self.sz) (x : M) (hij : j ≠ i) :
    (self.set i x).get ⟨j, by simp⟩ = self.get j := by
  exact Impl.setData_get_of_ne self i j x hij

def Valid (self : SegTree M op e) : Prop :=
  (∀ i : Fin self.cap, i.val ≠ 0 →
    self.data[i.val]'(by
      have hi := i.isLt
      have hc := self.cap_pos
      omega) =
      op (self.data[i.val * 2]'(by
        have hi := i.isLt
        omega))
      (self.data[i.val * 2 + 1]'(by
        have hi := i.isLt
        omega))) ∧
  (∀ i : Fin self.cap, self.sz ≤ i.val →
    self.data[self.cap + i.val]'(by
      have hi := i.isLt
      omega) = e)

theorem ofArray_Valid (op : M → M → M) (e : M) (a : Array M) : Valid (ofArray op e a) := by
  simp [Valid]
  constructor
  · intro i i0
    simp [ofArray, Fin.foldl_eq_finRange_foldl, Fin.foldr_eq_finRange_foldr]
    have hi : i.val < a.size.nextPowerOfTwo := i.isLt
    change (buildData op (List.finRange _) _)[i.val] =
      op (buildData op (List.finRange _) _)[i.val * 2]
        (buildData op (List.finRange _) _)[i.val * 2 + 1]
    exact buildData_valid _ (List.pairwise_lt_finRange _) _ i
      (List.mem_finRange i) i0
  ·
    simp [ofArray, Fin.foldl_eq_finRange_foldl, Fin.foldr_eq_finRange_foldr]
    intro i hsi
    have hi : i.val < a.size.nextPowerOfTwo := i.isLt
    let base : Vector M (a.size.nextPowerOfTwo * 2) :=
      Vector.replicate (a.size.nextPowerOfTwo * 2) e
    let leaves : Vector M (a.size.nextPowerOfTwo * 2) :=
      (List.finRange a.size).foldl
        (fun dat j => dat.set (a.size.nextPowerOfTwo + j.val) a[j.val]) base
    change (buildData op (List.finRange a.size.nextPowerOfTwo) leaves).get
      ⟨a.size.nextPowerOfTwo + i.val, by omega⟩ = e
    calc
      _ = leaves[a.size.nextPowerOfTwo + i.val] :=
        buildData_get_of_cap_le _ _ _ (by omega) (by omega)
      _ = base[a.size.nextPowerOfTwo + i.val] := by
        apply Vector.getElem_foldl_set_of_forall_ne (List.finRange a.size)
          (fun j => a.size.nextPowerOfTwo + j.val)
          (fun j => by
            change a.size.nextPowerOfTwo + j.val <
              a.size.nextPowerOfTwo * 2
            have hj := j.isLt
            have hs := Nat.le_nextPowerOfTwo a.size
            have hc : 0 < a.size.nextPowerOfTwo :=
              Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo a.size)
            omega)
          (fun j => a[j.val]) base _ (by omega)
        intro j hj
        have hj' := j.isLt
        omega
      _ = e := by simp [base]

theorem set_Valid (self : SegTree M op e) (hself : Valid self)
    (i : Fin self.sz) (x : M) : Valid (self.set i x) := by
  rcases hself with ⟨hinternal, hpadding⟩
  constructor
  · change internalValid op (Impl.setDataAt self i x)
    unfold Impl.setDataAt Impl.setData
    dsimp only
    split
    · intro k hk0
      have hi := i.isLt
      have hs := self.sz_le
      have hc := self.cap_pos
      omega
    · rename_i hroot
      apply Impl.modifyUpData_internalValid
      · change (self.cap + i.val) / 2 ≠ 0
        omega
      · intro k hk0 hkp
        have hkpv : k.val ≠ (self.cap + i.val) / 2 := by
          intro h
          apply hkp
          apply Fin.ext
          exact h
        rw [Vector.getElem_set_ne, Vector.getElem_set_ne,
          Vector.getElem_set_ne]
        · exact hinternal k hk0
        all_goals omega
  · change ∀ j : Fin self.cap, self.sz ≤ j.val →
      (Impl.setDataAt self i x)[self.cap + j.val] = e
    intro j hsj
    have hi := i.isLt
    have hj := j.isLt
    have hs := self.sz_le
    have hc := self.cap_pos
    unfold Impl.setDataAt Impl.setData
    dsimp only
    split
    · rw [Vector.getElem_set_ne]
      · exact hpadding j hsj
      · omega
    · change (Impl.modifyUpData op (self.data.set (self.cap + i.val) x _) _).get
        ⟨self.cap + j.val, by omega⟩ = e
      rw [Impl.modifyUpData_get_of_cap_le _ _ _ (by omega) (by omega)]
      change (self.data.set (self.cap + i.val) x _)[self.cap + j.val] = e
      rw [Vector.getElem_set_ne]
      · exact hpadding j hsj
      · omega

@[simp] theorem prod_of_ge (self : SegTree M op e)
    (l r : Fin (self.sz + 1)) (h : r ≤ l) : self.prod l r = e := by
  simp [prod, h]

@[simp] theorem prod_self (self : SegTree M op e)
    (i : Fin (self.sz + 1)) : self.prod i i = e := by
  exact prod_of_ge self i i (by rfl)

theorem prod_eq_leaf_range [Std.Associative op] [Std.LawfulIdentity op e]
    (self : SegTree M op e) (hvalid : Valid self)
    (l r : Fin (self.sz + 1)) :
    self.prod l r =
      ((List.range' (self.cap + l.val) (r.val - l.val)).map
        (fun j => self.data.getD j e)).foldr op e := by
  by_cases hlr : r ≤ l
  · have : r.val - l.val = 0 := by omega
    simp [prod_of_ge self l r hlr, this]
  · have hlr' : l.val < r.val := by omega
    rcases self.cap_pow2 with ⟨height, hcap⟩
    have hinter : internalValid op self.data := hvalid.1
    unfold prod
    simp only [if_neg (by omega : ¬ l ≥ r)]
    calc
      Impl.prod self 1 0 self.cap l.val r.val =
          Impl.prod self 1 0 (0 + 2 ^ height) l.val r.val := by
        congr
        omega
      _ = queryFold op e self.data 1 0 l.val r.val height :=
        Impl.prod_eq_queryFold self hinter height 1 0 l.val r.val
          (by omega) (by
            rw [hcap]
            exact Nat.le_of_eq (by ring))
      _ = foldOp op e ((List.range' (1 * 2 ^ height + (l.val - 0))
          (r.val - l.val)).map (fun j => self.data.getD j e)) :=
        queryFold_eq_range_prod self.data height 1 0 l.val r.val
          (by omega) (by
            have hr := r.isLt
            have hs := self.sz_le
            omega) hlr'
      _ = foldOp op e ((List.range' (self.cap + l.val) (r.val - l.val)).map
          (fun j => self.data.getD j e)) := by simp [hcap]

private theorem leafRange_eq_getRange (self : SegTree M op e)
    (start len : Nat) (hbound : start + len ≤ self.sz) :
    (List.range' (self.cap + start) len).map (fun j => self.data.getD j e) =
      (List.range' start len).map self.get! := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [List.range'_concat, List.range'_concat, List.map_append, List.map_append]
    congr 1
    · exact ih (by omega)
    · simp only [List.map_singleton, List.cons.injEq]
      have hk : start + len < self.sz := by omega
      have hs := self.sz_le
      have hc := self.cap_pos
      simp [get!, hk, get, Vector.getD, Array.getD]
      rw [dif_pos (by omega)]
      congr 1
      omega

theorem prod_eq_range_prod [Std.Associative op] [Std.LawfulIdentity op e]
    (self : SegTree M op e) (hvalid : Valid self)
    (l r : Fin (self.sz + 1)) :
    self.prod l r =
      ((List.range' l.val (r.val - l.val)).map self.get!).foldr op e := by
  rw [prod_eq_leaf_range self hvalid l r]
  apply congrArg (foldOp op e)
  apply leafRange_eq_getRange
  have hr := r.isLt
  omega

example :
    let tree := ofArray (· * ·) 1 #[2, 3, 5, 7]
    tree.allProd == 210 && tree.maxRight 0 (· ≤ 30) == 3 &&
      tree.minLeft 4 (· ≤ 35) == 2 && tree.maxRight 1 (· ≤ 15) == 3 &&
      tree.minLeft 3 (· ≤ 15) == 1 && tree.maxRight 4 (· ≤ 0) == 4 &&
      tree.minLeft 0 (· ≤ 0) == 0 := by
  native_decide

/-- In range, the `!` variants agree with the `Fin`-indexed originals; range bounds
accept `sz` while position-like arguments accept at most `sz - 1`. -/
example :
    let tree := ofArray (· * ·) 1 #[2, 3, 5, 7]
    tree.get! 2 == 5 && tree.prod! 1 3 == 15 && (tree.set! 0 11).get! 0 == 11 &&
      tree.maxRight! 0 (· ≤ 30) == 3 && tree.minLeft! 4 (· ≤ 35) == 2 := by
  native_decide

example :
    let tree := ofArray (· * ·) 1 #[2, 3, 5, 7]
    (tree.get? 3).isSome && (tree.get? 4).isNone &&
      (tree.set? 3 1).isSome && (tree.set? 4 1).isNone &&
      (tree.prod? 0 4).isSome && (tree.prod? 0 5).isNone &&
      (tree.maxRight? 4 (· ≤ 0)).isSome && (tree.maxRight? 5 (· ≤ 0)).isNone &&
      (tree.minLeft? 4 (· ≤ 0)).isSome && (tree.minLeft? 5 (· ≤ 0)).isNone := by
  native_decide

end SegTree

end Cplib
