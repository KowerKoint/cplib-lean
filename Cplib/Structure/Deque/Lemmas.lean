import Cplib.Structure.Deque.Basic
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.Deque.Lemmas

Specification of the deque in `Structure.Deque.Basic`.

Every operation is pinned to what it does to `toList`, the sequence the deque
stands for, so that reasoning about a deque reduces to reasoning about a list.
The two representations of a given sequence — elements sitting in `front` or in
`back` — are not distinguished by any of these statements, which is the point:
`toList` is the abstraction, and the split is an implementation detail.
-/

namespace Deque

variable {α : Type u} {d d' : Deque α} {x : α} {l : List α}

@[simp] theorem toList_mk (front back : List α) :
    (Deque.mk front back).toList = front ++ back.reverse := rfl

@[simp] theorem toList_empty : (empty : Deque α).toList = [] := rfl

@[simp] theorem toList_ofList (xs : List α) : (ofList xs).toList = xs := by
  simp [ofList]

@[simp] theorem toList_ofArray (xs : Array α) : (ofArray xs).toList = xs.toList := by
  simp [ofArray]

@[simp] theorem toArray_eq (d : Deque α) : d.toArray = d.toList.toArray := by
  simp [toArray, toList]

@[simp] theorem isEmpty_iff : d.isEmpty = true ↔ d.toList = [] := by
  cases d
  simp [isEmpty, toList]

@[simp] theorem size_eq_length_toList (d : Deque α) : d.size = d.toList.length := by
  cases d
  simp [size, toList]

@[simp] theorem toList_pushFront (d : Deque α) (x : α) :
    (d.pushFront x).toList = x :: d.toList := rfl

@[simp] theorem toList_pushBack (d : Deque α) (x : α) :
    (d.pushBack x).toList = d.toList ++ [x] := by
  cases d
  simp [pushBack, toList]

@[simp] theorem front?_eq_head? (d : Deque α) : d.front? = d.toList.head? := by
  cases d with
  | mk front back =>
      cases front with
      | cons x xs => simp [front?]
      | nil => simp [front?]

@[simp] theorem back?_eq_getLast? (d : Deque α) : d.back? = d.toList.getLast? := by
  cases d with
  | mk front back =>
      cases back with
      | cons x xs => simp [back?]
      | nil => simp [back?]

@[simp] theorem popFront?_eq_none_iff : d.popFront? = none ↔ d.toList = [] := by
  cases d with
  | mk front back =>
      cases front with
      | cons x xs => simp [popFront?]
      | nil =>
          cases hb : back.reverse with
          | nil => simp [popFront?, List.reverse_eq_nil_iff.mp hb]
          | cons y ys => simp [popFront?, hb]

/-- Popping the front takes the first element of `toList` and leaves the rest. -/
theorem toList_of_popFront? (h : d.popFront? = some (x, d')) :
    d.toList = x :: d'.toList := by
  cases d with
  | mk front back =>
      cases front with
      | cons y ys =>
          simp only [popFront?, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp
      | nil =>
          cases hb : back.reverse with
          | nil => simp [popFront?, hb] at h
          | cons y ys =>
              simp only [popFront?, hb, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [hb]

/-- Conversely, whenever `toList` is non-empty the pop succeeds and splits it. -/
theorem popFront?_of_toList (h : d.toList = x :: l) :
    ∃ d', d.popFront? = some (x, d') ∧ d'.toList = l := by
  cases d with
  | mk front back =>
      cases front with
      | cons y ys =>
          simp only [toList_mk, List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨ys, back⟩, by simp [popFront?]⟩
      | nil =>
          simp only [toList_mk, List.nil_append] at h
          exact ⟨⟨l, []⟩, by simp [popFront?, h], by simp⟩

@[simp] theorem isSome_popFront? : d.popFront?.isSome ↔ d.toList ≠ [] := by
  rw [Option.isSome_iff_ne_none, ne_eq, popFront?_eq_none_iff]

/-- Draining a deque from the front yields exactly `toList`.

The termination argument is the point of the exercise: `toList_of_popFront?`
turns the pop into `d.toList = x :: d'.toList`, and `size_eq_length_toList`
turns that into a decreasing measure. -/
private def drainNat (d : Deque Nat) : List Nat :=
  match _h : d.popFront? with
  | none => []
  | some (x, d') => x :: drainNat d'
termination_by d.size
decreasing_by
  have h := toList_of_popFront? _h
  simp only [size_eq_length_toList, h, List.length_cons]
  omega

/-- Regression test: the two ends interleave as expected. -/
example : ((Deque.empty.pushBack 2 |>.pushFront 1).pushBack 3).toList = [1, 2, 3] := by
  native_decide

/-- Regression test: popping from the front crosses from `front` into the
reversed `back` without disturbing the order. -/
example : drainNat ((Deque.ofList [2, 3]).pushFront 1 |>.pushBack 4) = [1, 2, 3, 4] := by
  native_decide

end Deque

end Cplib
