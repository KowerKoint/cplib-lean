import Cplib.Structure.RingBuffer.Basic
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.RingBuffer.Lemmas

Specification of the ring buffer in `Structure.RingBuffer.Basic`.

Every operation is pinned to what it does to `toList`, the sequence the buffer
stands for. Neither the capacity nor the slot the elements start at appears in
any of these statements: two buffers holding the same sequence are
interchangeable, however their slots happen to be arranged.

The one piece of arithmetic everything rests on is `slot_inj`, that distinct
indices below the capacity occupy distinct slots. Without it, writing one slot
could silently disturb another, and none of what follows would be true.
-/

namespace RingBuffer

variable {α : Type u} {b : RingBuffer α} {x : α}

/-! ### Slot arithmetic -/

/-- Indices below the capacity occupy distinct slots. -/
theorem slot_inj (b : RingBuffer α) {i j : Nat} (hi : i < b.cap) (hj : j < b.cap)
    (h : b.slot i = b.slot j) : i = j := by
  have hmod : i % b.cap = j % b.cap := Nat.ModEq.add_left_cancel' b.head h
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod

/-! ### `toList` -/

@[simp] theorem length_toList (b : RingBuffer α) : b.toList.length = b.sz := by
  simp [toList]

@[simp] theorem getElem_toList (b : RingBuffer α) (i : Nat) (h : i < b.toList.length) :
    b.toList[i] = b.get ⟨i, by simpa using h⟩ := by
  simp [toList]

@[simp] theorem toList_eq_nil_iff : b.toList = [] ↔ b.sz = 0 := by
  simp [toList, List.ofFn_eq_nil_iff]

/-- Two buffers holding the same elements in the same order have the same
`toList`, whatever their capacities and starting slots. -/
theorem ext_toList {b₁ b₂ : RingBuffer α} (hsz : b₁.sz = b₂.sz)
    (hget : ∀ i, (h₁ : i < b₁.sz) → (h₂ : i < b₂.sz) → b₁.get ⟨i, h₁⟩ = b₂.get ⟨i, h₂⟩) :
    b₁.toList = b₂.toList := by
  apply List.ext_getElem (by simp [hsz])
  intro i h₁ h₂
  rw [getElem_toList, getElem_toList]
  exact hget i _ _

@[simp] theorem size_eq_sz (b : RingBuffer α) : b.size = b.sz := rfl

@[simp] theorem toList_empty : (empty : RingBuffer α).toList = [] := rfl

@[simp] theorem isEmpty_iff : b.isEmpty = true ↔ b.toList = [] := by
  simp [isEmpty]

@[simp] theorem toList_ofArray (xs : Array α) : (ofArray xs).toList = xs.toList := by
  apply List.ext_getElem (by simp [ofArray])
  intro i h₁ h₂
  have hi : i < xs.size := by simpa using h₂
  simp [ofArray, get, slot, Nat.mod_eq_of_lt hi]

@[simp] theorem get?_eq_getElem? (b : RingBuffer α) (i : Nat) :
    b.get? i = b.toList[i]? := by
  by_cases h : i < b.sz <;> simp [get?, h]

@[simp] theorem front?_eq_head? (b : RingBuffer α) : b.front? = b.toList.head? := by
  simp [front?, List.head?_eq_getElem?]

@[simp] theorem back?_eq_getLast? (b : RingBuffer α) : b.back? = b.toList.getLast? := by
  simp [back?, List.getLast?_eq_getElem?]

/-! ### Growing

Growing moves every element to the front of a larger `data`, which leaves the
sequence alone. -/

@[simp] theorem Impl.toList_grow (b : RingBuffer α) (pad : α) :
    (Impl.grow b pad).toList = b.toList := by
  refine ext_toList (b₁ := Impl.grow b pad) (b₂ := b) (Impl.grow_sz b pad) ?_
  intro i h₁ h₂
  have hlt : i < (if b.cap = 0 then 1 else b.cap * 2) := by
    have := b.sz_le
    split <;> omega
  have hmod : i % (if b.cap = 0 then 1 else b.cap * 2) = i := Nat.mod_eq_of_lt hlt
  simp only [get, Impl.grow, slot, Nat.zero_add, Vector.getElem_ofFn]
  rw [dif_pos (show i % (if b.cap = 0 then 1 else b.cap * 2) < b.sz by rw [hmod]; exact h₂)]
  exact getElem_congr_idx (by rw [hmod])

/-! ### Pushing -/

theorem Impl.toList_pushBackIn (b : RingBuffer α) (h : b.sz < b.cap) (x : α) :
    (Impl.pushBackIn b h x).toList = b.toList ++ [x] := by
  apply List.ext_getElem (by simp [Impl.pushBackIn])
  intro i h₁ h₂
  have hi : i < b.sz + 1 := by simpa [Impl.pushBackIn] using h₁
  rw [getElem_toList]
  rcases Nat.lt_or_ge i b.sz with hlt | hge
  · have hne : (b.head + b.sz) % b.cap ≠ (b.head + i) % b.cap := fun he =>
      absurd (b.slot_inj h (Nat.lt_trans hlt h) he) (Nat.ne_of_gt hlt)
    rw [List.getElem_append_left (by simpa using hlt)]
    simp only [get, Impl.pushBackIn, slot, getElem_toList]
    rw [Vector.getElem_set_ne _ _ hne]
  · have hieq : i = b.sz := by omega
    subst hieq
    rw [List.getElem_append_right (by simp)]
    simp only [get, Impl.pushBackIn, slot, length_toList, Nat.sub_self]
    rw [Vector.getElem_set_self]
    simp

theorem Impl.toList_pushFrontIn (b : RingBuffer α) (h : b.sz < b.cap) (x : α) :
    (Impl.pushFrontIn b h x).toList = x :: b.toList := by
  have hcap : 0 < b.cap := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have hcapm1 : (b.head + b.cap - 1) % b.cap = (b.head + (b.cap - 1)) % b.cap := by
    congr 1
    omega
  apply List.ext_getElem (by simp [Impl.pushFrontIn])
  intro i h₁ h₂
  have hi : i < b.sz + 1 := by simpa [Impl.pushFrontIn] using h₁
  rw [getElem_toList]
  cases i with
  | zero =>
      have hz : ((b.head + b.cap - 1) % b.cap + 0) % b.cap = (b.head + b.cap - 1) % b.cap := by
        rw [Nat.add_zero]
        exact Nat.mod_mod_of_dvd _ (dvd_refl _)
      simp only [get, Impl.pushFrontIn, slot, List.getElem_cons_zero]
      rw [Vector.getElem_set, if_pos hz.symm]
  | succ j =>
      have hj : j < b.sz := by omega
      -- Shifting the start back by one and the index forward by one cancel.
      have hslot : ((b.head + b.cap - 1) % b.cap + (j + 1)) % b.cap = (b.head + j) % b.cap := by
        rw [Nat.mod_add_mod, show b.head + b.cap - 1 + (j + 1) = b.head + j + b.cap by omega,
          Nat.add_mod_right]
      have hne : (b.head + b.cap - 1) % b.cap ≠ (b.head + j) % b.cap := by
        rw [hcapm1]
        intro he
        have hcm : b.cap - 1 = j :=
          b.slot_inj (i := b.cap - 1) (j := j)
            (Nat.sub_lt hcap Nat.one_pos) (Nat.lt_trans hj h) he
        omega
      have hST : (b.head + b.cap - 1) % b.cap
          ≠ ((b.head + b.cap - 1) % b.cap + (j + 1)) % b.cap := by
        rw [hslot]
        exact hne
      simp only [get, Impl.pushFrontIn, slot, List.getElem_cons_succ, getElem_toList]
      rw [Vector.getElem_set, if_neg hST]
      exact getElem_congr_idx hslot

@[simp] theorem toList_pushBack (b : RingBuffer α) (x : α) :
    (b.pushBack x).toList = b.toList ++ [x] := by
  unfold pushBack
  split
  · exact Impl.toList_pushBackIn _ _ _
  · rw [Impl.toList_pushBackIn, Impl.toList_grow]

@[simp] theorem toList_pushFront (b : RingBuffer α) (x : α) :
    (b.pushFront x).toList = x :: b.toList := by
  unfold pushFront
  split
  · exact Impl.toList_pushFrontIn _ _ _
  · rw [Impl.toList_pushFrontIn, Impl.toList_grow]

/-! ### Updating -/

@[simp] theorem toList_set (b : RingBuffer α) (i : Fin b.sz) (x : α) :
    (b.set i x).toList = b.toList.set i.val x := by
  apply List.ext_getElem (by simp [RingBuffer.set])
  intro j h₁ h₂
  have hj : j < b.sz := by simpa using h₁
  rw [getElem_toList, List.getElem_set]
  by_cases hij : i.val = j
  · subst hij
    simp only [get, RingBuffer.set, slot]
    rw [Vector.getElem_set_self]
    simp
  · have hne : (b.head + i.val) % b.cap ≠ (b.head + j) % b.cap := fun he =>
      hij (b.slot_inj (Nat.lt_of_lt_of_le i.isLt b.sz_le)
        (Nat.lt_of_lt_of_le hj b.sz_le) he)
    simp only [if_neg hij, get, RingBuffer.set, slot, getElem_toList]
    rw [Vector.getElem_set_ne _ _ hne]

/-! ### Popping -/

@[simp] theorem popFront?_eq_none_iff : b.popFront? = none ↔ b.sz = 0 := by
  unfold popFront?
  split <;> rename_i h <;> simp <;> omega

@[simp] theorem popBack?_eq_none_iff : b.popBack? = none ↔ b.sz = 0 := by
  unfold popBack?
  split <;> rename_i h <;> simp <;> omega

/-- Popping the front takes the first element of `toList` and leaves the rest. -/
theorem toList_of_popFront? {b b' : RingBuffer α} {x : α}
    (h : b.popFront? = some (x, b')) : b.toList = x :: b'.toList := by
  unfold popFront? at h
  split at h
  · rename_i hpos
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    cases i with
    | zero => simp
    | succ j =>
        have hj : j + 1 < b.sz := by simpa using h₁
        rw [getElem_toList, List.getElem_cons_succ, getElem_toList]
        simp only [get, slot]
        exact getElem_congr_idx (by rw [Nat.mod_add_mod]; congr 1; omega)
  · simp at h

/-- Popping the back takes the last element of `toList` and leaves the rest. -/
theorem toList_of_popBack? {b b' : RingBuffer α} {x : α}
    (h : b.popBack? = some (x, b')) : b.toList = b'.toList ++ [x] := by
  unfold popBack? at h
  split at h
  · rename_i hpos
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    have hi : i < b.sz := by simpa using h₁
    rw [getElem_toList]
    rcases Nat.lt_or_ge i (b.sz - 1) with hlt | hge
    · rw [List.getElem_append_left (by simpa using hlt)]
      simp [get, slot]
    · have hieq : i = b.sz - 1 := by omega
      subst hieq
      rw [List.getElem_append_right (by simp)]
      simp [get, slot]
  · simp at h

@[simp] theorem isSome_popFront? : b.popFront?.isSome ↔ b.toList ≠ [] := by
  rw [Option.isSome_iff_ne_none, ne_eq, popFront?_eq_none_iff, ne_eq, toList_eq_nil_iff]

@[simp] theorem isSome_popBack? : b.popBack?.isSome ↔ b.toList ≠ [] := by
  rw [Option.isSome_iff_ne_none, ne_eq, popBack?_eq_none_iff, ne_eq, toList_eq_nil_iff]

/-! ### Regression tests -/

/-- Move `k` elements from the front to the back, which walks `head` past the
end of `data` and back round. -/
private def cycleNat : Nat → RingBuffer Nat → RingBuffer Nat
  | 0, b => b
  | k + 1, b =>
      match b.popFront? with
      | none => b
      | some (x, b') => cycleNat k (b'.pushBack x)

/-- Drain from the back, which `popBack?` leaves `head` alone for. -/
private def drainBackNat (b : RingBuffer Nat) : List Nat :=
  match _h : b.popBack? with
  | none => []
  | some (x, b') => x :: drainBackNat b'
termination_by b.sz
decreasing_by
  have h := toList_of_popBack? _h
  have := congrArg List.length h
  simp only [length_toList, List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- Regression test: pushes at both ends and the growth they force. -/
example : ((RingBuffer.empty.pushBack 2 |>.pushFront 1).pushBack 3).toList = [1, 2, 3] := by
  native_decide

/-- Regression test: `head` walking past the end of `data` does not disturb the
order. Ten rotations of four elements is two. -/
example : (cycleNat 10 (RingBuffer.ofArray #[0, 1, 2, 3])).toList = [2, 3, 0, 1] := by
  native_decide

/-- Regression test: draining from the back yields the elements back to front,
across a buffer whose live range wraps. -/
example : drainBackNat (cycleNat 3 (RingBuffer.ofArray #[0, 1, 2, 3, 4])) = [2, 1, 0, 4, 3] := by
  native_decide

/-- Regression test: random access reads the element the sequence says it should,
including after the range wraps. -/
example : (cycleNat 3 (RingBuffer.ofArray #[0, 1, 2, 3, 4])).get! 1 = 4 := by
  native_decide

end RingBuffer

end Cplib
