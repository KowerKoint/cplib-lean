import Cplib.Util.Container.Basic

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

theorem runLengthEncode_length [BEq α] (xs : List α) :
    (xs.runLengthEncode.map (·.2) |>.sum) = xs.length := by
  induction xs with
  | nil =>
    simp [List.runLengthEncode]
  | cons x xs hxs =>
    simp [List.runLengthEncode]
    match hr : xs.runLengthEncode with
    | [] =>
      simp
      rw [hr] at hxs
      simp at hxs
      exact List.length_eq_zero_iff.mp hxs.symm
    | (a, c) :: tail =>
      simp
      split
      · simp [List.map_cons]
        rw [hr] at hxs
        simp [List.map_cons] at hxs
        omega
      · simp [List.map_cons]
        rw [hr] at hxs
        simp [List.map_cons] at hxs
        omega

theorem runLengthEncode_recover [DecidableEq α] (xs : List α) :
    xs.runLengthEncode.flatMap (fun (a, c) => List.replicate c a) = xs := by
  induction xs with
  | nil =>
    simp [List.runLengthEncode]
  | cons x xs hxs =>
    simp [List.runLengthEncode]
    split
    · rename_i hr
      simp
      rw [hr] at hxs
      simp at hxs
      omega
    · rename_i hr
      split
      · rename_i h
        simp [List.flatMap_cons]
        rw [hr] at hxs
        simp [List.flatMap_cons] at hxs
        rw [List.replicate,h,←hxs]
        simp [List.cons_append]
      · simp [List.flatMap_cons]
        rw [hr] at hxs
        simp [List.flatMap_cons] at hxs
        omega

theorem runLengthEncode_positive [BEq α] (xs : List α) :
    xs.runLengthEncode.all (·.2 > 0) := by
  induction xs with
  | nil =>
    simp [List.runLengthEncode]
  | cons x xs hxs =>
    simp only [List.runLengthEncode]
    split
    · simp
    · rename_i a c tail hr
      split
      · simp [List.all_cons]
        rw [hr] at hxs
        simp [List.all_cons] at hxs
        exact hxs.right
      · simp [List.all_cons]
        rw [hr] at hxs
        simp [List.all_cons] at hxs
        omega

/-- Run-length encoding のキーには、元のリストの要素がちょうど一度ずつ現れる。 -/
theorem mem_runLengthEncode_keys [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) :
    a ∈ xs.runLengthEncode.map (·.1) ↔ a ∈ xs := by
  induction xs with
  | nil => simp [List.runLengthEncode]
  | cons x xs ih =>
      simp [List.runLengthEncode]
      split
      · rename_i hr
        have hax : a ∉ xs := by
          intro ha
          have := ih.mpr ha
          simp [hr] at this
        simp [hax]
      · rename_i b c tail hr
        have ih' : (a = b ∨ a ∈ tail.map (·.1)) ↔ a ∈ xs := by
          simpa [hr] using ih
        split
        · rename_i hxb
          have hxb' : x = b := LawfulBEq.eq_of_beq hxb
          subst b
          constructor
          · rintro ⟨k, hk⟩
            simp only [List.mem_cons, Prod.mk.injEq] at hk
            rcases hk with ⟨hax, _⟩ | hk
            · exact Or.inl hax
            · exact Or.inr (ih'.mp (Or.inr
                (List.mem_map.mpr ⟨(a, k), hk, rfl⟩)))
          · intro ha
            rcases ha with hax | ha
            · subst a
              exact ⟨c + 1, by simp⟩
            · rcases ih'.mpr ha with hax | htail
              · subst a
                exact ⟨c + 1, by simp⟩
              · obtain ⟨⟨b, k⟩, hk, hab⟩ := List.mem_map.mp htail
                simp only at hab
                subst b
                exact ⟨k, by simp [hk]⟩
        · constructor
          · rintro ⟨k, hk⟩
            simp only [List.mem_cons, Prod.mk.injEq] at hk
            rcases hk with ⟨hax, _⟩ | ⟨hab, _⟩ | hk
            · exact Or.inl hax
            · exact Or.inr (ih'.mp (Or.inl hab))
            · exact Or.inr (ih'.mp (Or.inr
                (List.mem_map.mpr ⟨(a, k), hk, rfl⟩)))
          · intro ha
            rcases ha with hax | ha
            · subst a
              exact ⟨1, by simp⟩
            · rcases ih'.mpr ha with hab | htail
              · subst a
                exact ⟨c, by simp⟩
              · obtain ⟨⟨b', k⟩, hk, hab⟩ := List.mem_map.mp htail
                simp only at hab
                subst b'
                exact ⟨k, by simp [hk]⟩

theorem mem_uniqueSorted [Ord α] [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) :
    a ∈ xs.uniqueSorted ↔ a ∈ xs := by
  simp only [List.uniqueSorted, mem_runLengthEncode_keys]
  exact List.mem_mergeSort

def distinctWithNeighbor [BEq α] : List (α × Nat) → Prop
| [] => True
| [_] => True
| a :: b :: xs => a.1 ≠ b.1 ∧ distinctWithNeighbor (b :: xs)

theorem runLengthEncode_distinctWithNeighbor [BEq α] [LawfulBEq α] (xs : List α) :
    distinctWithNeighbor xs.runLengthEncode := by
  induction xs with
  | nil =>
    simp [List.runLengthEncode, distinctWithNeighbor]
  | cons x xs hxs =>
    simp [List.runLengthEncode]
    split
    · simp [distinctWithNeighbor]
    · rename_i a c tail hr
      split
      · rw [hr] at hxs
        rcases tail
        · simp [distinctWithNeighbor]
        · rename_i bd tail
          let (b, d) := bd
          simp [distinctWithNeighbor]
          simp [distinctWithNeighbor] at hxs
          omega
      · rename_i h
        simp [distinctWithNeighbor]
        constructor
        · simp at h
          omega
        · rw [hr] at hxs
          omega

namespace Array

theorem mem_uniqueSorted [Ord α] [BEq α] [LawfulBEq α]
    (xs : Array α) (a : α) :
    a ∈ xs.uniqueSorted ↔ a ∈ xs := by
  simp [Array.uniqueSorted, _root_.mem_uniqueSorted]

end Array
