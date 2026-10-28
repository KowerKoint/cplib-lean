import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.FinRange

namespace List

/-- Bringing the element at `k` to the front, and putting `a` where it was,
permutes the list. -/
private theorem perm_getElem_cons_set (a : α) : ∀ (l : List α) (k : Nat) (hk : k < l.length),
    (l[k] :: l.set k a).Perm (a :: l) := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons b s ih =>
      intro k hk
      cases k with
      | zero => simpa using List.Perm.swap a b s
      | succ m =>
          have hm : m < s.length := by simpa using hk
          calc (b :: s)[m + 1] :: (b :: s).set (m + 1) a
              = s[m] :: b :: s.set m a := by simp
            _ ~ b :: s[m] :: s.set m a := List.Perm.swap _ _ _
            _ ~ b :: a :: s := List.Perm.cons b (ih m hm)
            _ ~ a :: b :: s := List.Perm.swap _ _ _

/-- Exchanging the elements at two indices permutes the list. -/
private theorem perm_set_set : ∀ (l : List α) (i j : Nat) (hi : i < l.length)
    (hj : j < l.length), ((l.set i l[j]).set j l[i]).Perm l := by
  intro l
  induction l with
  | nil => intro i j hi _; simp at hi
  | cons a t ih =>
      intro i j hi hj
      cases i with
      | zero =>
          cases j with
          | zero => simp
          | succ k =>
              have hk : k < t.length := by simpa using hj
              simpa using perm_getElem_cons_set a t k hk
      | succ m =>
          have hm : m < t.length := by simpa using hi
          cases j with
          | zero => simpa using perm_getElem_cons_set a t m hm
          | succ k =>
              have hk : k < t.length := by simpa using hj
              simpa using List.Perm.cons a (ih m k hm hk)

end List

namespace Vector

/-- `Vector.swap` only permutes, so it preserves the multiset of elements. -/
theorem toList_swap_perm (v : Vector α n) (i j : Fin n) :
    (v.swap i j).toList.Perm v.toList := by
  rw [Vector.toList_swap]
  exact List.perm_set_set v.toList i.val j.val (by simp) (by simp)

/-- Folding `Vector.set` leaves every index untouched that none of the updates
targets. -/
theorem getElem_foldl_set_of_forall_ne {N : Nat} {I : Type}
    (xs : List I) (idx : I → Nat) (hidx : ∀ x, idx x < N) (value : I → α)
    (data : Vector α N) (j : Nat) (hj : j < N)
    (hne : ∀ x ∈ xs, idx x ≠ j) :
    (xs.foldl (fun dat x => dat.set (idx x) (value x) (hidx x)) data).get ⟨j, hj⟩ =
      data.get ⟨j, hj⟩ := by
  induction xs generalizing data with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    · change (data.set (idx x) (value x) (hidx x))[j] = data[j]
      rw [Vector.getElem_set_ne]
      exact hne x (by simp)
    · intro y hy
      exact hne y (by simp [hy])

/-- Folding `Vector.set` over distinct indices leaves each target holding the value
it was given. -/
theorem getElem_foldl_set_of_mem {N : Nat} {I : Type}
    (xs : List I) (idx : I → Nat) (hidx : ∀ x, idx x < N) (value : I → α)
    (data : Vector α N) (x : I) (hx : x ∈ xs) (hnodup : xs.Nodup)
    (hinj : ∀ y ∈ xs, idx y = idx x → y = x) :
    (xs.foldl (fun dat y => dat.set (idx y) (value y) (hidx y)) data).get
      ⟨idx x, hidx x⟩ = value x := by
  induction xs generalizing data with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.nodup_cons] at hnodup
    rcases hx with h | hx
    · subst y
      simp only [List.foldl_cons]
      rw [Vector.getElem_foldl_set_of_forall_ne]
      · exact Vector.getElem_set_self _
      · intro z hz hzx
        have := hinj z (by simp [hz]) hzx
        subst z
        exact hnodup.1 hz
    · apply ih (data := data.set (idx y) (value y) (hidx y)) hx hnodup.2
      intro z hz hzx
      exact hinj z (by simp [hz]) hzx

/-- An index loop of `Vector.set` over every `Fin n`, as `Fin.foldl` runs one,
leaves each index holding the value it was given.

Implementations use `Fin.foldl` because it allocates nothing; the proof goes
through `List.finRange` and `getElem_foldl_set_of_mem`. -/
theorem getElem_foldl_set_fin {N n : Nat} (hidx : ∀ i : Fin n, i.val < N)
    (value : Fin n → α) (data : Vector α N) (j : Fin n) :
    (Fin.foldl n (fun v i => v.set i.val (value i) (hidx i)) data).get ⟨j.val, hidx j⟩
      = value j := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact getElem_foldl_set_of_mem (List.finRange n) Fin.val hidx value data j
    (List.mem_finRange j) (List.nodup_finRange n) (fun y _ hy => Fin.ext hy)

end Vector
