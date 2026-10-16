import Cplib.Structure.Heap.Basic
import Mathlib.Tactic

/-!
# Structure.Heap.Lemmas

`Structure.Heap.Basic` の二分ヒープに関する基本的な仕様。
-/

namespace Heap

variable {α : Type}

/-- 比較器が表す非狭義順序。 -/
def LE (heap : Heap α) (x y : α) : Prop :=
  (heap.cmp x y).isLE

/-- 各頂点の値がその親の値以上である、最小ヒープ条件。 -/
def Valid (heap : Heap α) : Prop :=
  ∀ i : Fin heap.n, i.val ≠ 0 →
    heap.LE (heap.data.get ⟨(i.val - 1) / 2, by omega⟩) (heap.data.get i)

/-- `Valid` なヒープの根は、比較器が表す順序で全要素以下である。 -/
theorem top_le (heap : Heap α) (hvalid : heap.Valid)
    (hrefl : Reflexive heap.LE) (htrans : Transitive heap.LE)
    (hpos : 0 < heap.n) (i : Fin heap.n) :
    heap.LE (heap.top hpos) heap.data[i] := by
  have go : ∀ k, (hk : k < heap.n) →
      heap.LE (heap.data.get ⟨0, hpos⟩) (heap.data.get ⟨k, hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases hk0 : k = 0
        · subst k
          exact hrefl _
        · let p := (k - 1) / 2
          have hp_lt_k : p < k := by
            dsimp [p]
            omega
          have hp : p < heap.n := Nat.lt_trans hp_lt_k hk
          exact htrans (ih p hp_lt_k hp)
            (hvalid ⟨k, hk⟩ hk0)
  exact go i.val i.isLt

@[simp] theorem empty_Valid (cmp : α → α → Ordering) :
    (empty cmp).Valid := by
  intro i _
  exact Fin.elim0 i

@[simp] theorem Impl.modifyUp_n (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyUp heap idx).n = heap.n := by
  fun_induction Impl.modifyUp <;> simp_all

@[simp] theorem Impl.modifyUp_cmp (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyUp heap idx).cmp = heap.cmp := by
  fun_induction Impl.modifyUp <;> simp_all

@[simp] theorem Impl.modifyDown_n (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyDown heap idx).n = heap.n := by
  fun_induction Impl.modifyDown <;> simp_all

@[simp] theorem Impl.modifyDown_cmp (heap : Heap α) (idx : Fin heap.n) :
    (Impl.modifyDown heap idx).cmp = heap.cmp := by
  fun_induction Impl.modifyDown <;> simp_all

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

@[simp] theorem ofArray_n (xs : Array α) (cmp : α → α → Ordering) :
    (ofArray xs cmp).n = xs.size := by
  unfold ofArray
  rw [← Array.foldl_toList]
  have go (ys : List α) (heap : Heap α) :
      (ys.foldl (fun heap x => heap.add x) heap).n = heap.n + ys.length := by
    induction ys generalizing heap with
    | nil => simp
    | cons y ys ih =>
        simp only [List.foldl_cons]
        rw [ih]
        simp only [add_n, List.length_cons]
        omega
  rw [go]
  simp

@[simp] theorem ofArray_cmp (xs : Array α) (cmp : α → α → Ordering) :
    (ofArray xs cmp).cmp = cmp := by
  unfold ofArray
  rw [← Array.foldl_toList]
  have go (ys : List α) (heap : Heap α) :
      (ys.foldl (fun heap x => heap.add x) heap).cmp = heap.cmp := by
    induction ys generalizing heap with
    | nil => rfl
    | cons y ys ih =>
        simp only [List.foldl_cons]
        rw [ih]
        simp
  rw [go]
  rfl

@[simp] theorem pop_n (heap : Heap α) (h : 0 < heap.n) :
    (heap.pop h).n = heap.n - 1 := by
  simp [pop]
  split <;> simp

@[simp] theorem pop_cmp (heap : Heap α) (h : 0 < heap.n) :
    (heap.pop h).cmp = heap.cmp := by
  simp [pop]
  split <;> simp

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

end Heap
