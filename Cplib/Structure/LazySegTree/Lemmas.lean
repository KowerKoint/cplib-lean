import Cplib.Structure.LazySegTree.Basic
import Cplib.Structure.SegTree.Lemmas
import Mathlib.Tactic

namespace Cplib

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

private theorem Impl.push_data_root [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) :
    (Impl.push data lazy i).1.getD i 1 = data.getD i 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega)]

private theorem Impl.push_data_left [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push data lazy i).1.getD (i * 2) 1 =
      lazy.getD i 1 • data.getD (i * 2) 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_data_right [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push data lazy i).1.getD (i * 2 + 1) 1 =
      lazy.getD i 1 • data.getD (i * 2 + 1) 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_root [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push data lazy i).2.getD i 1 = 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_data_of_ne [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i j : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hleft : i * 2 ≠ j) (hright : i * 2 + 1 ≠ j) :
    (Impl.push data lazy i).1.getD j 1 = data.getD j 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ hright,
    Impl.getD_setD_of_ne _ _ _ hleft]

private theorem Impl.push_lazy_left [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap) :
    (Impl.push data lazy i).2.getD (i * 2) 1 =
      lazy.getD i 1 * lazy.getD (i * 2) 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_right [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push data lazy i).2.getD (i * 2 + 1) 1 =
      lazy.getD i 1 * lazy.getD (i * 2 + 1) 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_of_ne [Mul M] [One M] [Mul F] [One F] [SMul F M]
    {cap i j : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hleft : i * 2 ≠ j) (hright : i * 2 + 1 ≠ j) (hroot : i ≠ j) :
    (Impl.push data lazy i).2.getD j 1 = lazy.getD j 1 := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ hroot,
    Impl.getD_setD_of_ne _ _ _ hright,
    Impl.getD_setD_of_ne _ _ _ hleft]

private theorem Impl.push_internalAt [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap) (hvalid : internalAt data lazy i) :
    let result := Impl.push data lazy i
    internalAt result.1 result.2 i := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_root data lazy hi0, Impl.push_lazy_root data lazy hi,
    Impl.push_data_left data lazy hi, Impl.push_data_right data lazy hi]
  rw [one_smul, ← MulDistribMulAction.smul_mul]
  exact hvalid

private theorem Impl.push_internalAt_left [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i * 2 < cap)
    (hvalid : internalAt data lazy (i * 2)) :
    let result := Impl.push data lazy i
    internalAt result.1 result.2 (i * 2) := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_left data lazy (by omega),
    Impl.push_lazy_left data lazy hi0 (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    mul_smul, hvalid, MulDistribMulAction.smul_mul]

private theorem Impl.push_internalAt_right [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i * 2 + 1 < cap)
    (hvalid : internalAt data lazy (i * 2 + 1)) :
    let result := Impl.push data lazy i
    internalAt result.1 result.2 (i * 2 + 1) := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_right data lazy (by omega),
    Impl.push_lazy_right data lazy (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    mul_smul, hvalid, MulDistribMulAction.smul_mul]

private theorem Impl.push_internalAt_away [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hroot : j ≠ i) (hleft : j ≠ i * 2) (hright : j ≠ i * 2 + 1)
    (hvalid : internalAt data lazy j) :
    let result := Impl.push data lazy i
    internalAt result.1 result.2 j := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_of_ne data lazy hleft.symm hright.symm,
    Impl.push_lazy_of_ne data lazy hleft.symm hright.symm hroot.symm,
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega)]
  exact hvalid

private theorem Impl.push_internalValid [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap)
    (hvalid : ∀ j, j ≠ 0 → j < cap → internalAt data lazy j) :
    let result := Impl.push data lazy i
    ∀ j, j ≠ 0 → j < cap → internalAt result.1 result.2 j := by
  dsimp only
  intro j hj0 hj
  by_cases hji : j = i
  · subst j
    exact Impl.push_internalAt data lazy hi0 hi (hvalid i hi0 hi)
  by_cases hjl : j = i * 2
  · subst j
    exact Impl.push_internalAt_left data lazy hi0 hj
      (hvalid (i * 2) (by omega) hj)
  by_cases hjr : j = i * 2 + 1
  · subst j
    exact Impl.push_internalAt_right data lazy hj
      (hvalid (i * 2 + 1) (by omega) hj)
  exact Impl.push_internalAt_away data lazy hji hjl hjr (hvalid j hj0 hj)

private theorem Impl.push_preserves_one [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) (hj : data.getD j 1 = 1) :
    (Impl.push data lazy i).1.getD j 1 = 1 := by
  by_cases hjl : j = i * 2
  · subst j
    rw [Impl.push_data_left data lazy hi, hj, MulDistribMulAction.smul_one]
  by_cases hjr : j = i * 2 + 1
  · subst j
    rw [Impl.push_data_right data lazy hi, hj, MulDistribMulAction.smul_one]
  rw [Impl.push_data_of_ne data lazy (by omega) (by omega), hj]

/- During a recursive range update, only ancestors of the current subtree may
temporarily fail their node equation.  Parameterising the exceptional nodes
keeps that temporary state explicit. -/
private def internalValidOutside [Monoid M] [Monoid F] [MulDistribMulAction F M]
    {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) : Prop :=
  ∀ j, j ≠ 0 → j < cap → ¬ except j → internalAt data lazy j

private theorem Impl.push_internalValidOutside [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) (hi0 : i ≠ 0) (hi : i < cap)
    (hvalid : internalValidOutside data lazy except) :
    let result := Impl.push data lazy i
    internalValidOutside result.1 result.2 except := by
  dsimp only
  intro j hj0 hj hjex
  by_cases hji : j = i
  · subst j
    exact Impl.push_internalAt data lazy hi0 hi (hvalid i hi0 hi hjex)
  by_cases hjl : j = i * 2
  · subst j
    exact Impl.push_internalAt_left data lazy hi0 hj
      (hvalid (i * 2) (by omega) hj hjex)
  by_cases hjr : j = i * 2 + 1
  · subst j
    exact Impl.push_internalAt_right data lazy hj
      (hvalid (i * 2 + 1) (by omega) hj hjex)
  exact Impl.push_internalAt_away data lazy hji hjl hjr
    (hvalid j hj0 hj hjex)

private theorem Impl.applyNode_internalValidOutside [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (except : Nat → Prop) (hi0 : i ≠ 0)
    (hvalid : internalValidOutside data lazy except) :
    let result := Impl.applyNode data lazy i f
    internalValidOutside result.1 result.2
      (fun j => except j ∨ j = i / 2) := by
  dsimp only
  intro j hj0 hj hjex
  have hje : ¬ except j := fun h => hjex (Or.inl h)
  have hjp : j ≠ i / 2 := fun h => hjex (Or.inr h)
  by_cases hji : j = i
  · subst j
    exact Impl.applyNode_internalAt data lazy f hi0 hj (hvalid i hi0 hj hje)
  apply Impl.applyNode_internalAt_of_away data lazy f hji
  · intro h
    apply hjp
    omega
  · intro h
    apply hjp
    omega
  · exact hvalid j hj0 hj hje

private theorem Impl.repair_internalValidOutside [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) (hi : i < cap)
    (hlazy : lazy.getD i 1 = 1)
    (hvalid : internalValidOutside data lazy (fun j => except j ∨ j = i)) :
    internalValidOutside
      (Impl.setD data i (data.getD (i * 2) 1 * data.getD (i * 2 + 1) 1)) lazy
      (fun j => except j ∨ j = i / 2) := by
  intro j hj0 hj hjex
  have hje : ¬ except j := fun h => hjex (Or.inl h)
  have hjp : j ≠ i / 2 := fun h => hjex (Or.inr h)
  by_cases hji : j = i
  · subst j
    unfold internalAt
    rw [Impl.getD_setD_self _ _ _ (by omega),
      Impl.getD_setD_of_ne _ _ _ (by omega),
      Impl.getD_setD_of_ne _ _ _ (by omega)]
    rw [hlazy, one_smul]
  · unfold internalAt
    rw [Impl.getD_setD_of_ne _ _ _ (fun h => hji h.symm),
      Impl.getD_setD_of_ne _ _ _ (by
        intro h
        apply hjp
        omega),
      Impl.getD_setD_of_ne _ _ _ (by
        intro h
        apply hjp
        omega)]
    exact hvalid j hj0 hj (by simp [hje, hji])

private theorem Impl.applyRange_lazy_of_lt [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap : Nat} (f : F) (ql qr : Nat) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)) (j : Nat), j < i →
      (Impl.applyRange f ql qr fuel i l r data lazy).2.getD j 1 =
        lazy.getD j 1 := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro i l r data lazy j hji
      rw [Impl.applyRange]
      split
      · rfl
      · split
        · simp only [Impl.applyNode]
          rw [Impl.getD_setD_of_ne _ _ _ (by omega)]
        · let pushed := Impl.push data lazy i
          let mid := l + (r - l) / 2
          let left := Impl.applyRange f ql qr fuel (i * 2) l mid pushed.1 pushed.2
          let right := Impl.applyRange f ql qr fuel (i * 2 + 1) mid r left.1 left.2
          change right.2.getD j 1 = lazy.getD j 1
          rw [ih (i * 2 + 1) mid r left.1 left.2 j (by omega),
            ih (i * 2) l mid pushed.1 pushed.2 j (by omega)]
          dsimp only [pushed]
          rw [Impl.push_lazy_of_ne data lazy (by omega) (by omega) (by omega)]

private theorem Impl.applyRange_internalValidOutside [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap : Nat} (f : F) (ql qr : Nat) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)) (except : Nat → Prop),
      i ≠ 0 → r ≤ cap → (r - l).isPowerOfTwo → i * (r - l) = cap + l →
      internalValidOutside data lazy except →
      let result := Impl.applyRange f ql qr fuel i l r data lazy
      internalValidOutside result.1 result.2
        (fun j => except j ∨ j = i / 2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i l r data lazy except hi0 hrcap hp hcap hvalid
      simp only [Impl.applyRange]
      intro j hj0 hj hjex
      exact hvalid j hj0 hj (fun he => hjex (Or.inl he))
  | succ fuel ih =>
      intro i l r data lazy except hi0 hrcap hp hcap hvalid
      rw [Impl.applyRange]
      split
      · dsimp only
        intro j hj0 hj hjex
        exact hvalid j hj0 hj (fun he => hjex (Or.inl he))
      · rename_i hdisjoint
        split
        · exact Impl.applyNode_internalValidOutside data lazy f except hi0 hvalid
        · rename_i hfull
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            not_or, not_and_or] at hdisjoint hfull
          obtain ⟨k, hk⟩ := hp
          cases k with
          | zero =>
              simp only [pow_zero] at hk
              have : ql ≤ l ∧ r ≤ qr := by omega
              rcases hfull with h | h <;> omega
          | succ k =>
              let mid := l + (r - l) / 2
              have hd : r - l = 2 ^ k * 2 := by
                simpa [Nat.pow_succ] using hk
              have hil : i < cap := by
                have : 0 < i := Nat.pos_of_ne_zero hi0
                have hkpos : 0 < 2 ^ k := pow_pos (by omega) _
                have hlr : l < r := by
                  omega
                have hr : r = l + 2 ^ k * 2 := by omega
                rw [hd] at hcap
                nlinarith
              let pushed := Impl.push data lazy i
              have hvp : internalValidOutside pushed.1 pushed.2 except :=
                Impl.push_internalValidOutside data lazy except hi0 hil hvalid
              have hmid : mid = l + 2 ^ k := by
                dsimp [mid]
                omega
              have hleftPow : (mid - l).isPowerOfTwo := ⟨k, by omega⟩
              have hrightPow : (r - mid).isPowerOfTwo := ⟨k, by omega⟩
              have hml : mid - l = 2 ^ k := by omega
              have hrm : r - mid = 2 ^ k := by omega
              have hleftCap : (i * 2) * (mid - l) = cap + l := by
                calc
                  (i * 2) * (mid - l) = (i * 2) * 2 ^ k := by rw [hml]
                  _ = i * (2 ^ k * 2) := by ring
                  _ = cap + l := by simpa [hd] using hcap
              have hrightCap : (i * 2 + 1) * (r - mid) = cap + mid := by
                have hdcap : i * (2 ^ k * 2) = cap + l := by
                  simpa [hd] using hcap
                calc
                  (i * 2 + 1) * (r - mid) = (i * 2 + 1) * 2 ^ k := by rw [hrm]
                  _ = i * (2 ^ k * 2) + 2 ^ k := by ring
                  _ = cap + mid := by rw [hmid, hdcap]; omega
              let left := Impl.applyRange f ql qr fuel (i * 2) l mid pushed.1 pushed.2
              have hvl : internalValidOutside left.1 left.2
                  (fun j => except j ∨ j = i) := by
                simpa [left] using
                  ih (i * 2) l mid pushed.1 pushed.2 except (by omega)
                    (by omega) hleftPow hleftCap hvp
              let right := Impl.applyRange f ql qr fuel (i * 2 + 1) mid r left.1 left.2
              have hvr : internalValidOutside right.1 right.2
                  (fun j => except j ∨ j = i) := by
                have h := ih (i * 2 + 1) mid r left.1 left.2
                  (fun j => except j ∨ j = i) (by omega) hrcap hrightPow hrightCap hvl
                have hparent : (i * 2 + 1) / 2 = i := by omega
                simpa [right, hparent, or_assoc] using h
              change internalValidOutside
                (Impl.setD right.1 i
                  (right.1.getD (i * 2) 1 * right.1.getD (i * 2 + 1) 1))
                right.2 (fun j => except j ∨ j = i / 2)
              apply Impl.repair_internalValidOutside right.1 right.2 except hil
              · rw [Impl.applyRange_lazy_of_lt f ql qr fuel (i * 2 + 1) mid r
                    left.1 left.2 i (by omega),
                  Impl.applyRange_lazy_of_lt f ql qr fuel (i * 2) l mid
                    pushed.1 pushed.2 i (by omega)]
                exact Impl.push_lazy_root data lazy hil
              · exact hvr

private def paddingValid [One M] {cap : Nat} (data : Vector M (cap * 2))
    (sz : Nat) : Prop :=
  ∀ x, sz ≤ x → x < cap → data.getD (cap + x) 1 = 1

private theorem Impl.applyRange_paddingValid [Monoid M] [Monoid F]
    [MulDistribMulAction F M] {cap sz : Nat} (f : F) (ql qr : Nat)
    (hqr : qr ≤ sz) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)),
      i ≠ 0 → r ≤ cap → (r - l).isPowerOfTwo →
      i * (r - l) = cap + l → paddingValid data sz →
      paddingValid (Impl.applyRange f ql qr fuel i l r data lazy).1 sz := by
  intro fuel
  induction fuel with
  | zero => intros; assumption
  | succ fuel ih =>
      intro i l r data lazy hi0 hrcap hp hcap hpadding
      rw [Impl.applyRange]
      split
      · exact hpadding
      · rename_i hdisjoint
        split
        · rename_i hfull
          intro x hsx hx
          simp only [Impl.applyNode]
          rw [Impl.getD_setD_of_ne]
          · exact hpadding x hsx hx
          · intro heq
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
              not_or] at hdisjoint hfull
            have hlr : l < r := by
              have := Nat.pos_of_isPowerOfTwo hp
              omega
            have hil : l < qr := by omega
            have hid : r - l = 1 := by
              by_contra hne
              have hd2 : 2 ≤ r - l := by omega
              have hic : cap ≤ i := by omega
              have hprod : cap * 2 ≤ i * (r - l) :=
                Nat.mul_le_mul hic hd2
              omega
            have hir : i = cap + l := by
              rw [hid] at hcap
              simpa using hcap
            omega
        · rename_i hfull
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            not_or, not_and_or] at hdisjoint hfull
          obtain ⟨k, hk⟩ := hp
          cases k with
          | zero =>
              simp only [pow_zero] at hk
              have : ql ≤ l ∧ r ≤ qr := by omega
              rcases hfull with h | h <;> omega
          | succ k =>
              let mid := l + (r - l) / 2
              have hd : r - l = 2 ^ k * 2 := by
                simpa [Nat.pow_succ] using hk
              have hkpos : 0 < 2 ^ k := pow_pos (by omega) _
              have hil : i < cap := by
                have hi : 0 < i := Nat.pos_of_ne_zero hi0
                have hlr : l < r := by omega
                rw [hd] at hcap
                nlinarith
              let pushed := Impl.push data lazy i
              have hpadPush : paddingValid pushed.1 sz := by
                intro x hsx hx
                exact Impl.push_preserves_one data lazy hil (hpadding x hsx hx)
              have hmid : mid = l + 2 ^ k := by
                dsimp [mid]
                omega
              have hml : mid - l = 2 ^ k := by omega
              have hrm : r - mid = 2 ^ k := by omega
              have hleftCap : (i * 2) * (mid - l) = cap + l := by
                calc
                  (i * 2) * (mid - l) = (i * 2) * 2 ^ k := by rw [hml]
                  _ = i * (2 ^ k * 2) := by ring
                  _ = cap + l := by simpa [hd] using hcap
              have hrightCap : (i * 2 + 1) * (r - mid) = cap + mid := by
                have hdcap : i * (2 ^ k * 2) = cap + l := by
                  simpa [hd] using hcap
                calc
                  (i * 2 + 1) * (r - mid) = (i * 2 + 1) * 2 ^ k := by rw [hrm]
                  _ = i * (2 ^ k * 2) + 2 ^ k := by ring
                  _ = cap + mid := by rw [hmid, hdcap]; omega
              let left := Impl.applyRange f ql qr fuel (i * 2) l mid pushed.1 pushed.2
              have hpadLeft : paddingValid left.1 sz :=
                ih (i * 2) l mid pushed.1 pushed.2 (by omega) (by omega)
                  ⟨k, hml⟩ hleftCap hpadPush
              let right := Impl.applyRange f ql qr fuel (i * 2 + 1) mid r left.1 left.2
              have hpadRight : paddingValid right.1 sz :=
                ih (i * 2 + 1) mid r left.1 left.2 (by omega) hrcap
                  ⟨k, hrm⟩ hrightCap hpadLeft
              intro x hsx hx
              change (Impl.setD right.1 i
                (right.1.getD (i * 2) 1 * right.1.getD (i * 2 + 1) 1)).getD
                  (cap + x) 1 = 1
              rw [Impl.getD_setD_of_ne _ _ _ (by omega)]
              exact hpadRight x hsx hx

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

/-- A lazy range update preserves the representation invariant. -/
theorem applyRange_Valid [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (self : LazySegTree M F) (hself : self.Valid)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).Valid := by
  let result := Impl.applyRange f l r self.cap 1 0 self.cap self.data self.lazy
  have hinternal : internalValidOutside self.data self.lazy (fun _ => False) := by
    intro i hi0 hi _
    exact hself.internalAt i hi0 hi
  have hout := Impl.applyRange_internalValidOutside f l r self.cap 1 0 self.cap
    self.data self.lazy (fun _ => False) (by omega) (by omega)
    self.cap_pow2 (by simp) hinternal
  have hpadding : paddingValid self.data self.sz := by
    intro i hsi hi
    exact hself.padding i hsi hi
  have hpadout := Impl.applyRange_paddingValid f l r (by omega) self.cap 1 0 self.cap
    self.data self.lazy (by omega) (by omega) self.cap_pow2 (by simp) hpadding
  change Valid { self with data := result.1, lazy := result.2 }
  constructor
  · intro i hi0
    have h := hout i.val hi0 i.isLt (by simp [result, hi0])
    unfold internalAt Vector.getD Array.getD at h
    simp only [Vector.size_toArray] at h
    rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega),
      dif_pos (by omega)] at h
    simpa only [result] using h
  · intro i hsi
    have hi : i.val < self.cap := i.isLt
    have hsi' : self.sz ≤ i.val := by simpa using hsi
    have h := hpadout i.val hsi' hi
    unfold Vector.getD Array.getD at h
    simp only [Vector.size_toArray] at h
    rw [dif_pos (by omega)] at h
    simpa only [result] using h

/-- A point update is the singleton special case of a valid range update. -/
theorem apply_Valid [Monoid M] [Monoid F] [MulDistribMulAction F M]
    (self : LazySegTree M F) (hself : self.Valid)
    (i : Fin self.sz) (f : F) : (self.apply i f).Valid := by
  unfold apply
  exact applyRange_Valid self hself _ _ f

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

end Cplib
