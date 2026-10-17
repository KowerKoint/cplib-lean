import Mathlib.Tactic

namespace Vector

private theorem List.perm_swap [BEq α] [LawfulBEq α]
    (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  rw [List.perm_iff_count]
  intro a
  rw [List.count_set (by simpa using hj), List.count_set hi]
  simp only [List.getElem_set]
  by_cases hij : i = j
  · subst j
    simp only
    by_cases hia : l[i] == a
    · have hc : 0 < l.count a := List.count_pos_iff.mpr (by
        have hia' : l[i] = a := by simpa using hia
        rw [← hia']
        exact List.getElem_mem hi)
      simp only [hia, if_true]
      omega
    · simp [hia]
  · simp only [if_neg hij]
    by_cases hia : l[i] == a <;> by_cases hja : l[j] == a
    · have hc : 0 < l.count a := List.count_pos_iff.mpr (by
        have hia' : l[i] = a := by simpa using hia
        rw [← hia']
        exact List.getElem_mem hi)
      simp only [hia, hja, if_true]
      omega
    · have hc : 0 < l.count a := List.count_pos_iff.mpr (by
        have hia' : l[i] = a := by simpa using hia
        rw [← hia']
        exact List.getElem_mem hi)
      simp only [hia, hja, if_true]
      omega
    · simp [hia, hja]
    · simp [hia, hja]

/-- `Vector.swap` は要素の順列だけを変え、内容の多重集合を保存する。 -/
theorem toList_swap_perm [BEq α] [LawfulBEq α]
    (v : Vector α n) (i j : Fin n) :
    (v.swap i j).toList.Perm v.toList := by
  rw [Vector.toList_swap]
  exact List.perm_swap v.toList i.val j.val (by simp) (by simp)

/-- `Vector.set` を畳み込んでも、どの更新対象とも異なる添字の値は変わらない。 -/
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

/-- 相異なる添字を順に `Vector.set` すると、更新対象の値は指定値になる。 -/
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

end Vector
