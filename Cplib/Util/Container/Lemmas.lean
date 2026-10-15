import Cplib.Util.Container.Basic

namespace Vector

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
