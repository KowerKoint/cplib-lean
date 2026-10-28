import Cplib.Structure.Heap.Basic
import Cplib.Util.Vector.Lemmas
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.Heap.Lemmas

Specification of the binary heap in `Structure.Heap.Basic`.

The comparator is data, not a typeclass, so every order statement here carries
its assumption about it explicitly: `LawfulCmp heap.cmp`. Under that assumption
`empty`, `add`, `pop` and `ofArray` all produce heaps satisfying `Valid`, and a
`Valid` heap's `top` is a minimum (`top_le`). `drain` then empties such a heap
into a sorted list (`drain_sorted`), which makes `ofArray` followed by `drain`
a verified heapsort (`drain_ofArray_sorted`, `drain_ofArray_perm`).
-/

namespace Heap

variable {α : Type}

/-! ## The comparator -/

/-- The non-strict order a comparator stands for. -/
def LE (cmp : α → α → Ordering) (x y : α) : Prop :=
  (cmp x y).isLE

/-- What the heap asks of its comparator: that `LE` is a preorder, and that
`cmp x y = .gt` and `cmp y x = .lt` agree on which way a pair goes.

Together these make `LE` total, since `¬ LE cmp x y` forces `cmp x y = .gt`.
Nothing checks this at runtime; a comparator that breaks it still runs, it just
leaves the resulting order unspecified. `compare` on a `LinearOrder` satisfies
it (`lawfulCmp_compare`), and so does the reversed comparator that turns the
min-heap into a max-heap (`LawfulCmp.swap`). -/
structure LawfulCmp (cmp : α → α → Ordering) : Prop where
  refl : Reflexive (LE cmp)
  trans : Transitive (LE cmp)
  gt_swap : ∀ x y, cmp x y = .gt → cmp y x = .lt

/-- `.isLT` is the strict form of `.isLE`. -/
theorem le_of_isLT {cmp : α → α → Ordering} {x y : α} (h : (cmp x y).isLT) :
    LE cmp x y := by
  unfold LE
  cases hc : cmp x y <;> simp_all

/-- `LE` is total: a pair the comparator does not accept one way it accepts the
other. -/
theorem LawfulCmp.le_of_not_le {cmp : α → α → Ordering} (h : LawfulCmp cmp) {x y : α}
    (hn : ¬ LE cmp x y) : LE cmp y x := by
  have hgt : cmp x y = .gt := by
    unfold LE at hn
    cases hc : cmp x y <;> simp_all
  simp [LE, h.gt_swap x y hgt]

/-- The form the `modifyDown` comparison takes: failing `.isLT` one way gives
`.isLE` the other. -/
theorem LawfulCmp.le_of_not_lt {cmp : α → α → Ordering} (h : LawfulCmp cmp) {x y : α}
    (hn : ¬ (cmp x y).isLT) : LE cmp y x := by
  by_contra hc
  have hgt : cmp y x = .gt := by
    unfold LE at hc
    cases hy : cmp y x <;> simp_all
  simp_all [h.gt_swap y x hgt]

/-- `LE compare` is the order of the `LinearOrder` it comes from. -/
theorem le_compare_iff [LinearOrder α] {x y : α} :
    LE (compare : α → α → Ordering) x y ↔ x ≤ y := by
  rw [← compare_le_iff_le]
  unfold LE
  cases h : compare x y <;> simp_all

/-- `compare` on a `LinearOrder` is a lawful comparator, so `Heap.empty` on such
a type is a lawful min-heap. -/
theorem lawfulCmp_compare [LinearOrder α] : LawfulCmp (compare : α → α → Ordering) where
  refl _ := le_compare_iff.mpr le_rfl
  trans := by
    intro x y z hxy hyz
    exact le_compare_iff.mpr (le_trans (le_compare_iff.mp hxy) (le_compare_iff.mp hyz))
  gt_swap _ _ h := compare_lt_iff_lt.mpr (compare_gt_iff_gt.mp h)

/-- Reversing a lawful comparator is lawful, which is what makes
`Heap.empty (fun a b => compare b a)` a well-behaved max-heap. -/
theorem LawfulCmp.swap {cmp : α → α → Ordering} (h : LawfulCmp cmp) :
    LawfulCmp (fun a b => cmp b a) where
  refl _ := h.refl _
  trans := by
    intro x y z hxy hyz
    exact h.trans hyz hxy
  gt_swap x y hgt := h.gt_swap y x hgt

/-! ## The heap order -/

/-- The min-heap property: every node is at least its parent under `cmp`. -/
def Valid (heap : Heap α) : Prop :=
  ∀ i : Nat, (h : i < heap.n) → i ≠ 0 →
    LE heap.cmp heap.data[(i - 1) / 2] heap.data[i]

/-- `Valid` restricted to the nodes whose parent sits at index `b` or later.

This is what bottom-up heapification has established once it has sifted down at
`b`, and it is how `Impl.modifyDown` is specified: `Valid` is the case `b = 0`.
-/
def ValidFrom (heap : Heap α) (b : Nat) : Prop :=
  ∀ i : Nat, (h : i < heap.n) → i ≠ 0 → b ≤ (i - 1) / 2 →
    LE heap.cmp heap.data[(i - 1) / 2] heap.data[i]

theorem valid_iff_validFrom_zero (heap : Heap α) : heap.Valid ↔ heap.ValidFrom 0 :=
  ⟨fun h i hi hi0 _ => h i hi hi0, fun h i hi hi0 => h i hi hi0 (Nat.zero_le _)⟩

/-- In a `Valid` heap the root is at most every element under `cmp`, so `top` really
is the minimum. -/
theorem top_le (heap : Heap α) (hlaw : LawfulCmp heap.cmp) (hvalid : heap.Valid)
    (hpos : 0 < heap.n) (i : Nat) (hi : i < heap.n) :
    LE heap.cmp (heap.top hpos) heap.data[i] := by
  induction i using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        exact hlaw.refl _
      · exact hlaw.trans (ih ((k - 1) / 2) (by omega) (by omega)) (hvalid k hi hk0)

/-- The same, for an element given by membership rather than by index. -/
theorem top_le_of_mem (heap : Heap α) (hlaw : LawfulCmp heap.cmp) (hvalid : heap.Valid)
    (hpos : 0 < heap.n) {b : α} (hb : b ∈ heap.data.toList) :
    LE heap.cmp (heap.top hpos) b := by
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hb
  rw [Vector.length_toList] at hj
  rw [Vector.getElem_toList] at hje
  rw [← hje]
  exact top_le heap hlaw hvalid hpos j hj

@[simp] theorem empty_Valid (cmp : α → α → Ordering) : (empty cmp).Valid := by
  intro i hi
  exact absurd hi (by simp [empty])

/-! ## Shape and contents -/

@[simp] theorem Impl.modifyUp_n (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyUp heap idx).n = heap.n := by
  fun_induction Impl.modifyUp <;> simp_all

@[simp] theorem Impl.modifyUp_cmp (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyUp heap idx).cmp = heap.cmp := by
  fun_induction Impl.modifyUp <;> simp_all

theorem Impl.modifyUp_data_perm (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyUp heap idx).data.toList.Perm heap.data.toList := by
  fun_induction Impl.modifyUp <;> simp_all
  apply List.Perm.trans (by assumption)
  apply Vector.toList_swap_perm

@[simp] theorem Impl.modifyDown_n (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyDown heap idx).n = heap.n := by
  fun_induction Impl.modifyDown <;> simp_all

@[simp] theorem Impl.modifyDown_cmp (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyDown heap idx).cmp = heap.cmp := by
  fun_induction Impl.modifyDown <;> simp_all

theorem Impl.modifyDown_data_perm (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyDown heap idx).data.toList.Perm heap.data.toList := by
  fun_induction Impl.modifyDown <;> simp_all
  all_goals
    apply List.Perm.trans (by assumption)
    apply Vector.toList_swap_perm

@[simp] theorem empty_n (cmp : α → α → Ordering) :
    (empty cmp).n = 0 := rfl

@[simp] theorem empty_data (cmp : α → α → Ordering) :
    (empty cmp).data = #v[] := rfl

@[simp] theorem empty_cmp (cmp : α → α → Ordering) :
    (empty cmp).cmp = cmp := rfl

@[simp] theorem size_eq_n (heap : Heap α) : heap.size = heap.n := rfl

@[simp] theorem isEmpty_eq_true (heap : Heap α) :
    heap.isEmpty = true ↔ heap.n = 0 := by
  simp [isEmpty]

@[simp] theorem add_n (heap : Heap α) (x : α) :
    (heap.add x).n = heap.n + 1 := by
  simp [add]

@[simp] theorem add_cmp (heap : Heap α) (x : α) :
    (heap.add x).cmp = heap.cmp := by
  simp [add]

theorem add_data_perm (heap : Heap α) (x : α) :
    (heap.add x).data.toList.Perm (heap.data.toList ++ [x]) := by
  unfold add
  apply List.Perm.trans (Impl.modifyUp_data_perm _ _)
  rw [Vector.toList_push]

/-! ## `modifyUp`, and `add` -/

/-- `Impl.modifyUp`'s loop invariant: the heap order holds at every node but `j`,
and `j`'s parent is already below each of `j`'s children.

The second clause is what the first swap needs. When the element at `j` trades
places with its parent, the parent's value lands on top of `j`'s children, and
nothing in the first clause says it belongs there. -/
def Impl.UpInv (heap : Heap α) (j : Nat) : Prop :=
  (∀ i : Nat, (h : i < heap.n) → i ≠ 0 → i ≠ j →
      LE heap.cmp heap.data[(i - 1) / 2] heap.data[i]) ∧
  (∀ c : Nat, (h : c < heap.n) → (hj : j < heap.n) → j ≠ 0 → (c - 1) / 2 = j →
      LE heap.cmp heap.data[(j - 1) / 2] heap.data[c])

/-- Carrying an element up from `idx` restores the heap order. -/
theorem Impl.modifyUp_Valid : ∀ (heap : Heap α) (idx : Fin heap.n),
    LawfulCmp heap.cmp → Impl.UpInv heap idx.val → (Impl.modifyUp heap idx).Valid := by
  intro heap idx
  fun_induction Impl.modifyUp heap idx with
  | case1 h idx h0 =>
      -- At the root there is no parent left to compare against.
      simp only [Fin.toNat] at h0
      intro _ hinv i hi hi0
      exact hinv.1 i hi hi0 (by omega)
  | case2 h idx h0 par hle =>
      -- The parent is already below `idx`, so the only missing edge is in place.
      intro _ hinv i hi hi0
      by_cases hik : i = idx.val
      · subst hik
        simpa using hle
      · exact hinv.1 i hi hi0 hik
  | case3 h idx h0 par hgt ndata ih =>
      intro hlaw hinv
      simp only [Fin.toNat] at h0
      have hpk : (par : Nat) = (idx.val - 1) / 2 := rfl
      have hp_lt : (par : Nat) < idx.val := by rw [hpk]; omega
      have hnd : ∀ j, (hj : j < h.n) →
          ndata[j] = if j = (par : Nat) then h.data[idx] else
            if j = idx.val then h.data[par] else h.data[j] := by
        intro j hj
        simp [ndata, Vector.getElem_swap]
      have hle_ki : LE h.cmp h.data[idx] h.data[par] := by
        refine hlaw.le_of_not_le ?_
        simpa [LE] using hgt
      refine ih hlaw ⟨?_, ?_⟩
      · intro i hi hi0 hip
        replace hi : i < h.n := hi
        show LE h.cmp ndata[(i - 1) / 2] ndata[i]
        rw [hnd ((i - 1) / 2) (by omega), hnd i hi, if_neg hip]
        by_cases hA : (i - 1) / 2 = (par : Nat)
        · rw [if_pos hA]
          by_cases hD : i = idx.val
          · -- `idx` moved into its parent's slot, and its own value below it.
            rw [if_pos hD]
            exact hle_ki
          · -- A sibling of `idx`: it was above the parent, which is above `idx`.
            rw [if_neg hD]
            have h1 := hinv.1 i hi hi0 hD
            simp only [hA] at h1
            exact hlaw.trans hle_ki h1
        · rw [if_neg hA]
          have hD : i ≠ idx.val := by omega
          rw [if_neg hD]
          by_cases hB : (i - 1) / 2 = idx.val
          · -- A child of `idx`, now under the old parent: the second clause.
            rw [if_pos hB]
            exact hinv.2 i hi idx.isLt h0 hB
          · rw [if_neg hB]
            exact hinv.1 i hi hi0 hD
      · intro c hc hp hp0 hcp
        replace hc : c < h.n := hc
        replace hp : (par : Nat) < h.n := hp
        show LE h.cmp ndata[((par : Nat) - 1) / 2] ndata[c]
        rw [hnd (((par : Nat) - 1) / 2) (by omega), hnd c hc,
          if_neg (by omega : ((par : Nat) - 1) / 2 ≠ (par : Nat)),
          if_neg (by omega : ((par : Nat) - 1) / 2 ≠ idx.val),
          if_neg (by omega : c ≠ (par : Nat))]
        have hgp := hinv.1 (par : Nat) hp hp0 (by omega)
        by_cases hck : c = idx.val
        · rw [if_pos hck]
          exact hgp
        · rw [if_neg hck]
          have h2 := hinv.1 c hc (by omega) hck
          simp only [hcp] at h2
          exact hlaw.trans hgp h2

/-- `add` keeps the heap order: the new element goes in at a leaf, which has no
children to violate, and is then carried up. -/
theorem add_Valid (heap : Heap α) (hlaw : LawfulCmp heap.cmp) (hvalid : heap.Valid) (x : α) :
    (heap.add x).Valid := by
  unfold add
  refine Impl.modifyUp_Valid _ _ hlaw ⟨?_, ?_⟩
  · intro i hi hi0 hin
    replace hi : i < heap.n + 1 := hi
    replace hin : i ≠ heap.n := hin
    show LE heap.cmp (heap.data.push x)[(i - 1) / 2] (heap.data.push x)[i]
    rw [Vector.getElem_push_lt (by omega), Vector.getElem_push_lt (by omega)]
    exact hvalid i (by omega) hi0
  · -- The new leaf has no children: they would sit past the end of the vector.
    intro c hc hn hn0 hcn
    replace hc : c < heap.n + 1 := hc
    replace hn0 : heap.n ≠ 0 := hn0
    replace hcn : (c - 1) / 2 = heap.n := hcn
    omega

/-! ## `modifyDown` -/

/-- `Impl.modifyDown`'s loop invariant, relative to a lower bound `b` on the
parent indices under consideration.

The heap order holds at every node whose parent is not `j`, and `j`'s parent is
already below `j`'s children. `b` is what makes the same statement serve both
callers: `pop` sifts down from the root with `b = 0` and wants `Valid` back,
while bottom-up heapification sifts down at `b` itself and only ever claims the
range it has reached. -/
def Impl.DownInv (heap : Heap α) (b : Nat) (j : Nat) : Prop :=
  (∀ i : Nat, (h : i < heap.n) → i ≠ 0 → b ≤ (i - 1) / 2 → (i - 1) / 2 ≠ j →
      LE heap.cmp heap.data[(i - 1) / 2] heap.data[i]) ∧
  (∀ c : Nat, (h : c < heap.n) → (hj : j < heap.n) → j ≠ 0 → b ≤ (j - 1) / 2 →
      (c - 1) / 2 = j → LE heap.cmp heap.data[(j - 1) / 2] heap.data[c])

/-- The child `modifyDown` descends into is at or below both children. -/
theorem Impl.le_min_child (heap : Heap α) (hlaw : LawfulCmp heap.cmp) (idx a b m : Fin heap.n)
    (ha : (a : Nat) = idx.val * 2 + 1) (hb : (b : Nat) = idx.val * 2 + 2)
    (hm : m = if _h : (heap.cmp heap.data[a] heap.data[b]).isLT = true then a else b) :
    ∀ c, (hc : c < heap.n) → c ≠ 0 → (c - 1) / 2 = idx.val →
      LE heap.cmp heap.data[m] heap.data[c] := by
  intro c hc hc0 hcq
  subst hm
  have hc12 : c = (a : Nat) ∨ c = (b : Nat) := by omega
  split <;> rename_i hlt <;> simp only [Fin.getElem_fin] at hlt ⊢ <;>
    rcases hc12 with hh | hh <;> subst hh
  · exact hlaw.refl _
  · exact le_of_isLT hlt
  · exact hlaw.le_of_not_lt hlt
  · exact hlaw.refl _

/-- Where `modifyDown` stops, the node is already below both its children, and
the whole range is in order. -/
theorem Impl.stop_ValidFrom (heap : Heap α) (b : Nat) (idx : Fin heap.n)
    (hchild : ∀ c, (hc : c < heap.n) → c ≠ 0 → (c - 1) / 2 = idx.val →
      LE heap.cmp heap.data[idx] heap.data[c])
    (hinv : Impl.DownInv heap b idx.val) : heap.ValidFrom b := by
  intro i hi hi0 hb
  by_cases hq : (i - 1) / 2 = idx.val
  · have hch := hchild i hi hi0 hq
    simp only [Fin.getElem_fin] at hch
    simp only [hq]
    exact hch
  · exact hinv.1 i hi hi0 hb hq

/-- Swapping a node with a child that is below it, and below its sibling, moves
the invariant down to that child. -/
theorem Impl.swap_DownInv (heap : Heap α) (b : Nat) (idx m : Fin heap.n)
    (hlaw : LawfulCmp heap.cmp)
    (hm : (m : Nat) = idx.val * 2 + 1 ∨ (m : Nat) = idx.val * 2 + 2)
    (hminle : ∀ c, (hc : c < heap.n) → c ≠ 0 → (c - 1) / 2 = idx.val →
      LE heap.cmp heap.data[m] heap.data[c])
    (hgt : ¬ LE heap.cmp heap.data[idx] heap.data[m])
    (hinv : Impl.DownInv heap b idx.val) :
    Impl.DownInv (⟨heap.n, heap.data.swap idx.val m.val idx.isLt m.isLt, heap.cmp⟩ :
      Heap α) b m.val := by
  have hmidx : idx.val < m.val := by omega
  have hle_mk : LE heap.cmp heap.data[m] heap.data[idx] := hlaw.le_of_not_le hgt
  simp only [Fin.getElem_fin] at hminle hle_mk
  have hnd : ∀ j, (hj : j < heap.n) →
      (heap.data.swap idx.val m.val idx.isLt m.isLt)[j] =
        if j = idx.val then heap.data[m.val] else
          if j = m.val then heap.data[idx.val] else heap.data[j] := by
    intro j hj
    simp [Vector.getElem_swap]
  refine ⟨?_, ?_⟩
  · intro i hi hi0 hb hq
    replace hi : i < heap.n := hi
    replace hq : (i - 1) / 2 ≠ m.val := hq
    show LE heap.cmp _ _
    rw [hnd ((i - 1) / 2) (by omega), hnd i hi]
    by_cases hik : i = idx.val
    · -- `idx` itself, now holding the child's value: the second clause.
      subst hik
      rw [if_neg (by omega : (idx.val - 1) / 2 ≠ idx.val),
        if_neg (by omega : (idx.val - 1) / 2 ≠ m.val), if_pos rfl]
      exact hinv.2 m.val m.isLt idx.isLt hi0 hb (by omega)
    · rw [if_neg hik]
      by_cases him : i = m.val
      · -- The child, now holding what was above it.
        rw [if_pos him, if_pos (by omega : (i - 1) / 2 = idx.val)]
        exact hle_mk
      · rw [if_neg him]
        by_cases hq2 : (i - 1) / 2 = idx.val
        · -- The sibling, now under the child we moved up.
          rw [if_pos hq2]
          exact hminle i hi hi0 hq2
        · rw [if_neg hq2, if_neg hq]
          exact hinv.1 i hi hi0 hb hq2
  · intro c hc hmlt hm0 hb hcm
    replace hc : c < heap.n := hc
    show LE heap.cmp _ _
    rw [hnd ((m.val - 1) / 2) (by omega), hnd c hc,
      if_pos (by omega : (m.val - 1) / 2 = idx.val),
      if_neg (by omega : c ≠ idx.val), if_neg (by omega : c ≠ m.val)]
    have h1 := hinv.1 c hc (by omega) (by omega) (by omega)
    simp only [hcm] at h1
    exact h1

/-- Sifting down from `idx` puts the range from `b` on in order. -/
theorem Impl.modifyDown_ValidFrom : ∀ (heap : Heap α) (idx : Fin heap.n) (b : Nat),
    LawfulCmp heap.cmp → Impl.DownInv heap b idx.val →
      (Impl.modifyDown heap idx).ValidFrom b := by
  intro heap idx b
  fun_induction Impl.modifyDown heap idx with
  | case1 h idx c1n c2n hc2 c1 c2 cmin hle =>
      -- Both children exist and `idx` is below the smaller one, so below both.
      intro hlaw hinv
      refine Impl.stop_ValidFrom h b idx ?_ hinv
      intro c hc hc0 hcq
      exact hlaw.trans hle
        (Impl.le_min_child h hlaw idx c1 c2 cmin rfl rfl rfl c hc hc0 hcq)
  | case2 h idx c1n c2n hc2 c1 c2 cmin hgt ndata ih =>
      intro hlaw hinv
      refine ih hlaw ?_
      refine Impl.swap_DownInv h b idx cmin hlaw ?_
        (Impl.le_min_child h hlaw idx c1 c2 cmin rfl rfl rfl) hgt hinv
      have e1 : (c1 : Nat) = idx.val * 2 + 1 := rfl
      have e2 : (c2 : Nat) = idx.val * 2 + 2 := rfl
      simp only [cmin]
      split
      · exact Or.inl e1
      · exact Or.inr e2
  | case3 h idx c1n c2n hc2 hc1 c1 hle =>
      -- Only the left child exists, and `idx` is below it.
      intro hlaw hinv
      refine Impl.stop_ValidFrom h b idx ?_ hinv
      intro c hc hc0 hcq
      have e1 : (c1 : Nat) = idx.val * 2 + 1 := rfl
      have e2 : ¬ (idx.val * 2 + 2 < h.n) := hc2
      have hcc : c = (c1 : Nat) := by omega
      subst hcc
      simpa using hle
  | case4 h idx c1n c2n hc2 hc1 c1 hgt ndata ih =>
      intro hlaw hinv
      refine ih hlaw ?_
      refine Impl.swap_DownInv h b idx c1 hlaw (Or.inl rfl) ?_ hgt hinv
      intro c hc hc0 hcq
      have e1 : (c1 : Nat) = idx.val * 2 + 1 := rfl
      have e2 : ¬ (idx.val * 2 + 2 < h.n) := hc2
      have hcc : c = (c1 : Nat) := by omega
      subst hcc
      simpa using hlaw.refl h.data[c1]
  | case5 h idx c1n c2n hc2 hc1 =>
      -- A leaf: it has no children to be above.
      intro hlaw hinv
      refine Impl.stop_ValidFrom h b idx ?_ hinv
      intro c hc hc0 hcq
      have e1 : ¬ (idx.val * 2 + 1 < h.n) := hc1
      exfalso
      omega

@[simp] theorem Impl.heapifyFrom_n (heap : Heap α) (k : Nat) :
    (Impl.heapifyFrom heap k).n = heap.n := by
  induction k generalizing heap with
  | zero => rfl
  | succ k ih =>
      rw [Impl.heapifyFrom]
      split
      · rw [ih, Impl.modifyDown_n]
      · exact ih heap

@[simp] theorem Impl.heapifyFrom_cmp (heap : Heap α) (k : Nat) :
    (Impl.heapifyFrom heap k).cmp = heap.cmp := by
  induction k generalizing heap with
  | zero => rfl
  | succ k ih =>
      rw [Impl.heapifyFrom]
      split
      · rw [ih, Impl.modifyDown_cmp]
      · exact ih heap

theorem Impl.heapifyFrom_data_perm (heap : Heap α) (k : Nat) :
    (Impl.heapifyFrom heap k).data.toList.Perm heap.data.toList := by
  induction k generalizing heap with
  | zero => exact List.Perm.refl _
  | succ k ih =>
      rw [Impl.heapifyFrom]
      by_cases h : k < heap.n
      · rw [dif_pos h]
        exact List.Perm.trans (ih _) (Impl.modifyDown_data_perm _ _)
      · rw [dif_neg h]
        exact ih heap

@[simp] theorem ofArray_n (xs : Array α) (cmp : α → α → Ordering) :
    (ofArray xs cmp).n = xs.size := by
  simp [ofArray]

@[simp] theorem ofArray_cmp (xs : Array α) (cmp : α → α → Ordering) :
    (ofArray xs cmp).cmp = cmp := by
  simp [ofArray]

theorem ofArray_data_perm (xs : Array α) (cmp : α → α → Ordering) :
    (ofArray xs cmp).data.toList.Perm xs.toList := by
  unfold ofArray
  exact Impl.heapifyFrom_data_perm _ _

/-- Bottom-up heapification: sifting down at `k - 1, …, 0` turns the order on the
range from `k` on into the order on the whole heap. -/
theorem Impl.heapifyFrom_ValidFrom : ∀ (k : Nat) (heap : Heap α), LawfulCmp heap.cmp →
    heap.ValidFrom k → (Impl.heapifyFrom heap k).ValidFrom 0 := by
  intro k
  induction k with
  | zero => exact fun _ _ hvf => hvf
  | succ k ih =>
      intro heap hlaw hvf
      rw [Impl.heapifyFrom]
      by_cases hk : k < heap.n
      · rw [dif_pos hk]
        refine ih _ (by rw [Impl.modifyDown_cmp]; exact hlaw) ?_
        refine Impl.modifyDown_ValidFrom heap ⟨k, hk⟩ k hlaw (?_ : Impl.DownInv heap k k)
        refine ⟨?_, ?_⟩
        · intro i hi hi0 hb hq
          exact hvf i hi hi0 (by omega)
        · -- `k`'s own parent sits below `k`, so this clause asks nothing.
          intro c hc hj hj0 hb hcj
          exact absurd hb (by omega)
      · rw [dif_neg hk]
        refine ih _ hlaw ?_
        intro i hi hi0 hb
        exact hvf i hi hi0 (by omega)

/-- `ofArray` heapifies bottom-up, so it produces a heap in order. -/
theorem ofArray_Valid (xs : Array α) (cmp : α → α → Ordering) (hlaw : LawfulCmp cmp) :
    (ofArray xs cmp).Valid := by
  rw [valid_iff_validFrom_zero]
  unfold ofArray
  refine Impl.heapifyFrom_ValidFrom _ _ hlaw ?_
  -- Everything past `xs.size / 2` is a leaf, so nothing is left to check.
  intro i hi hi0 hb
  replace hi : i < xs.size := hi
  exact absurd hb (by omega)

@[simp] theorem pop_n (heap : Heap α) (h : 0 < heap.n) :
    (heap.pop h).n = heap.n - 1 := by
  simp [pop]
  split <;> simp

@[simp] theorem pop_cmp (heap : Heap α) (h : 0 < heap.n) :
    (heap.pop h).cmp = heap.cmp := by
  simp [pop]
  split <;> simp

/-- `pop` removes one occurrence of `top` and keeps every other element. -/
theorem pop_data_perm (heap : Heap α) (h : 0 < heap.n) :
    ((heap.pop h).data.toList ++ [heap.top h]).Perm heap.data.toList := by
  let last : Fin heap.n := ⟨heap.n - 1, by omega⟩
  let swapped := heap.data.swap 0 last
  have hlast : swapped.toList.getLast (by
      intro he
      have he' := congrArg List.length he
      simp at he'
      omega) = heap.top h := by
    rw [List.getLast_eq_getElem]
    simp only [Vector.length_toList]
    change swapped[heap.n - 1] = heap.data[0]
    simp [swapped, last]
  have hpop : swapped.pop.toList ++ [heap.top h] = swapped.toList := by
    rw [Vector.toList_pop, ← hlast, List.dropLast_append_getLast]
  by_cases hp : 0 < heap.n - 1
  · let base : Heap α := ⟨heap.n - 1, swapped.pop, heap.cmp⟩
    have heq : heap.pop h = Impl.modifyDown base ⟨0, hp⟩ := by
      simp [pop, hp, base, swapped, last]
    rw [heq]
    apply List.Perm.trans
      (List.Perm.append_right [heap.top h] (Impl.modifyDown_data_perm base ⟨0, hp⟩))
    rw [hpop]
    dsimp [swapped]
    exact Vector.toList_swap_perm heap.data ⟨0, h⟩ last
  · let base : Heap α := ⟨heap.n - 1, swapped.pop, heap.cmp⟩
    have heq : heap.pop h = base := by
      simp [pop, hp, base, swapped, last]
    rw [heq, hpop]
    dsimp [swapped]
    exact Vector.toList_swap_perm heap.data ⟨0, h⟩ last

/-- `pop` keeps the heap order. -/
theorem pop_Valid (heap : Heap α) (hlaw : LawfulCmp heap.cmp) (hvalid : heap.Valid)
    (h : 0 < heap.n) : (heap.pop h).Valid := by
  unfold pop
  split
  · rename_i hp
    rw [valid_iff_validFrom_zero]
    refine Impl.modifyDown_ValidFrom _ ⟨0, hp⟩ 0 hlaw ⟨?_, ?_⟩
    · -- Away from the root the last element landing at index 0 changes nothing.
      intro i hi hi0 _ hq
      replace hi : i < heap.n - 1 := hi
      replace hq : (i - 1) / 2 ≠ 0 := hq
      show LE heap.cmp ((heap.data.swap 0 (heap.n - 1)).pop)[(i - 1) / 2]
        ((heap.data.swap 0 (heap.n - 1)).pop)[i]
      rw [Vector.getElem_pop, Vector.getElem_pop,
        Vector.getElem_swap_of_ne (by omega) (by omega),
        Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact hvalid i (by omega) hi0
    · intro c hc hj hj0 _ _
      exact absurd rfl hj0
  · rename_i hp
    intro i hi hi0
    replace hi : i < heap.n - 1 := hi
    exact absurd hi (by omega)

/-- Successive `pop`s come out in non-decreasing order: what `pop` removes is at
most what the next `pop` would remove.

The next `top` is still one of the heap's elements, and `top_le` puts the
current one below all of them. -/
theorem top_le_top_pop (heap : Heap α) (hlaw : LawfulCmp heap.cmp)
    (hvalid : heap.Valid) (h : 0 < heap.n) (h' : 0 < (heap.pop h).n) :
    LE heap.cmp (heap.top h) ((heap.pop h).top h') :=
  top_le_of_mem heap hlaw hvalid h
    ((pop_data_perm heap h).mem_iff.mp
      (List.mem_append_left _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem h'))))

@[simp] theorem top?_empty (cmp : α → α → Ordering) :
    (empty cmp).top? = none := rfl

@[simp] theorem pop?_empty (cmp : α → α → Ordering) :
    (empty cmp).pop? = none := by
  simp [pop?]

@[simp] theorem pop?_eq_some (heap : Heap α) (h : 0 < heap.n) :
    heap.pop? = some (heap.pop h) := by
  simp [pop?, h]

@[simp] theorem top?_eq_some_top (heap : Heap α) (h : 0 < heap.n) :
    heap.top? = some (heap.top h) := by
  simp [top?, top, h]

/-! ## `drain` -/

/-- Induction by popping: to prove something of every heap it is enough to prove
it of `heap` given it for `heap.pop`. -/
theorem pop_induction {motive : Heap α → Prop}
    (step : ∀ heap : Heap α, (∀ h : 0 < heap.n, motive (heap.pop h)) → motive heap)
    (heap : Heap α) : motive heap := by
  suffices hk : ∀ k (heap : Heap α), heap.n ≤ k → motive heap from hk heap.n heap le_rfl
  intro k
  induction k with
  | zero => exact fun heap hk => step heap fun h => absurd h (by omega)
  | succ k ih =>
      exact fun heap hk => step heap fun h => ih (heap.pop h) (by rw [pop_n]; omega)

/-- Any step count past `heap.n` drains the same list, which is what lets `drain`
pass `heap.n` and still satisfy the equation it would have had as a recursive
definition. -/
theorem Impl.drainFuel_congr : ∀ (k l : Nat) (heap : Heap α), heap.n ≤ k → heap.n ≤ l →
    Impl.drainFuel k heap = Impl.drainFuel l heap := by
  intro k
  induction k with
  | zero =>
      intro l heap hk hl
      cases l with
      | zero => rfl
      | succ l =>
          simp only [Impl.drainFuel]
          rw [dif_neg (by omega)]
  | succ k ih =>
      intro l heap hk hl
      cases l with
      | zero =>
          simp only [Impl.drainFuel]
          rw [dif_neg (by omega)]
      | succ l =>
          simp only [Impl.drainFuel]
          by_cases h : 0 < heap.n
          · rw [dif_pos h, dif_pos h,
              ih l (heap.pop h) (by rw [pop_n]; omega) (by rw [pop_n]; omega)]
          · rw [dif_neg h, dif_neg h]

/-- `drain` pops once and drains the rest. -/
theorem drain_eq (heap : Heap α) :
    heap.drain = if h : 0 < heap.n then heap.top h :: (heap.pop h).drain else [] := by
  unfold drain
  by_cases h : 0 < heap.n
  · rw [dif_pos h, Impl.drainFuel_congr heap.n (heap.n - 1 + 1) heap le_rfl (by omega)]
    simp only [Impl.drainFuel]
    rw [dif_pos h]
    congr 1
    exact Impl.drainFuel_congr (heap.n - 1) (heap.pop h).n (heap.pop h)
      (by rw [pop_n]) (by rw [pop_n])
  · rw [dif_neg h, show heap.n = 0 by omega]
    rfl

@[simp] theorem drain_empty (cmp : α → α → Ordering) : (empty cmp).drain = [] := rfl

@[simp] theorem drain_length (heap : Heap α) : heap.drain.length = heap.n := by
  induction heap using pop_induction with
  | step heap ih =>
      rw [drain_eq]
      by_cases h : 0 < heap.n
      · rw [dif_pos h, List.length_cons, ih h, pop_n]
        omega
      · rw [dif_neg h]
        have hn : heap.n = 0 := by omega
        simp [hn]

/-- `drain` hands back exactly the elements the heap held. -/
theorem drain_perm (heap : Heap α) :
    heap.drain.Perm heap.data.toList := by
  induction heap using pop_induction with
  | step heap ih =>
      rw [drain_eq]
      by_cases h : 0 < heap.n
      · rw [dif_pos h]
        refine List.Perm.trans ?_ (pop_data_perm heap h)
        exact ((List.perm_append_singleton _ _).symm).trans ((ih h).append_right _)
      · rw [dif_neg h]
        have hn : heap.data.toList = [] :=
          List.eq_nil_of_length_eq_zero (by simp; omega)
        rw [hn]

/-- Draining a heap in order yields a sorted list: not merely non-decreasing
step to step, but every element below every later one. -/
theorem drain_sorted : ∀ (heap : Heap α), LawfulCmp heap.cmp →
    heap.Valid → heap.drain.Sorted (LE heap.cmp) := by
  intro heap
  induction heap using pop_induction with
  | step heap ih =>
      intro hlaw hvalid
      rw [drain_eq]
      by_cases h : 0 < heap.n
      · rw [dif_pos h]
        refine List.sorted_cons.mpr ⟨?_, ?_⟩
        · -- What `pop` left behind is still part of the heap, and `top` is below
          -- all of it.
          intro b hb
          refine top_le_of_mem heap hlaw hvalid h ?_
          exact (pop_data_perm heap h).mem_iff.mp
            (List.mem_append_left _ ((drain_perm (heap.pop h)).subset hb))
        · have hsorted := ih h (by rw [pop_cmp]; exact hlaw) (pop_Valid heap hlaw hvalid h)
          rwa [pop_cmp] at hsorted
      · rw [dif_neg h]
        exact List.sorted_nil

/-- Heapsort: `ofArray` then `drain` sorts an array. -/
theorem drain_ofArray_sorted (xs : Array α) (cmp : α → α → Ordering)
    (hlaw : LawfulCmp cmp) : ((ofArray xs cmp).drain).Sorted (LE cmp) := by
  have hsorted := drain_sorted (ofArray xs cmp) (by rw [ofArray_cmp]; exact hlaw)
    (ofArray_Valid xs cmp hlaw)
  rwa [ofArray_cmp] at hsorted

/-- …and it sorts exactly the elements it was given. -/
theorem drain_ofArray_perm (xs : Array α) (cmp : α → α → Ordering) :
    ((ofArray xs cmp).drain).Perm xs.toList :=
  (drain_perm _).trans (ofArray_data_perm xs cmp)

/-- Regression test for the implementation itself. -/
example : (ofArray #[5, 1, 4, 1, 3]).drain = [1, 1, 3, 4, 5] := by
  native_decide

end Heap

end Cplib