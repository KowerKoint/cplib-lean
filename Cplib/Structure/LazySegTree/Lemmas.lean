import Cplib.Structure.LazySegTree.Basic
import Cplib.Structure.SegTree.Lemmas
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.LazySegTree.Lemmas

Specification of the lazy segment tree in `Structure.LazySegTree.Basic`.

`Valid` is the representation invariant: an internal node holds the action
recorded there applied to the product of its children, and the padding beyond
`sz` holds `e`. `ofArray` establishes it and `applyRange` keeps it, so every
state this API produces has it.

What the five functions are assumed to satisfy is stated, not assumed silently.
`op` and `comp` are monoids, as `Std.Associative` and `Std.LawfulIdentity`,
which the usual choices on `Nat` already carry; `LawfulAct` is the rest, how
the action composes and spreads over a product.
-/

namespace LazySegTree
variable {M F : Type} {op : M → M → M} {e : M} {comp : F → F → F} {noop : F} {act : F → M → M}

/-- What the theorems assume of the action.

`act` has to respect how actions compose, and spread over a product the way
applying it to each factor would, or a pending action resting at a node would
not mean the same as the actions on the leaves below it. `op` and `comp` being
monoids is stated separately, as `Std.Associative` and `Std.LawfulIdentity`. -/
class LawfulAct (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) : Prop where
  /-- Composed actions act one after the other. -/
  act_comp : ∀ f g x, act (comp f g) x = act f (act g x)
  /-- The identity action changes nothing. -/
  act_noop : ∀ x, act noop x = x
  /-- An action spreads over a product. -/
  act_op : ∀ f x y, act f (op x y) = op (act f x) (act f y)
  /-- …and leaves the identity alone. -/
  act_e : ∀ f, act f e = e

/-! Each law with its operations spelled out, so that a rewrite has a pattern
to match rather than a metavariable at the head. -/

variable (op e comp noop act) in
private theorem actComp [LawfulAct op e comp noop act] (f g : F) (x : M) :
    act (comp f g) x = act f (act g x) :=
  LawfulAct.act_comp (op := op) (e := e) (comp := comp) (noop := noop) (act := act) f g x

variable (op e comp noop act) in
private theorem actNoop [LawfulAct op e comp noop act] (x : M) : act noop x = x :=
  LawfulAct.act_noop (op := op) (e := e) (comp := comp) (noop := noop) (act := act) x

variable (op e comp noop act) in
private theorem actOp [LawfulAct op e comp noop act] (f : F) (x y : M) :
    act f (op x y) = op (act f x) (act f y) :=
  LawfulAct.act_op (op := op) (e := e) (comp := comp) (noop := noop) (act := act) f x y

variable (op e comp noop act) in
private theorem actE [LawfulAct op e comp noop act] (f : F) : act f e = e :=
  LawfulAct.act_e (op := op) (e := e) (comp := comp) (noop := noop) (act := act) f

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

private def internalAt (op : M → M → M) (e : M) (_comp : F → F → F) (noop : F)
    (act : F → M → M) {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (i : Nat) : Prop :=
  data.getD i e = act (lazy.getD i noop)
    (op (data.getD (i * 2) e) (data.getD (i * 2 + 1) e))

private theorem Impl.applyNode_internalAt [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (hi0 : i ≠ 0) (hi : i < cap) (hvalid : internalAt op e comp noop act data lazy i) :
    let result := Impl.applyNode e comp noop act data lazy i f
    internalAt op e comp noop act result.1 result.2 i := by
  simp only [Impl.applyNode]
  unfold internalAt
  rw [Impl.getD_setD_self _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega : i ≠ i * 2),
    Impl.getD_setD_of_ne _ _ _ (by omega : i ≠ i * 2 + 1)]
  rw [actComp op e comp noop act, hvalid, actOp op e comp noop act]

private theorem Impl.applyNode_internalAt_of_away [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (hji : j ≠ i) (hleft : j * 2 ≠ i) (hright : j * 2 + 1 ≠ i)
    (hvalid : internalAt op e comp noop act data lazy j) :
    let result := Impl.applyNode e comp noop act data lazy i f
    internalAt op e comp noop act result.1 result.2 j := by
  simp only [Impl.applyNode]
  unfold internalAt
  rw [Impl.getD_setD_of_ne _ _ _ hji.symm,
    Impl.getD_setD_of_ne _ _ _ hji.symm,
    Impl.getD_setD_of_ne _ _ _ hleft.symm,
    Impl.getD_setD_of_ne _ _ _ hright.symm]
  exact hvalid

private theorem Impl.push_data_root 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) :
    (Impl.push e comp noop act data lazy i).1.getD i e = data.getD i e := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega)]

private theorem Impl.push_data_left 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push e comp noop act data lazy i).1.getD (i * 2) e =
      act (lazy.getD i noop) (data.getD (i * 2) e) := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_data_right 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push e comp noop act data lazy i).1.getD (i * 2 + 1) e =
      act (lazy.getD i noop) (data.getD (i * 2 + 1) e) := by
  simp only [Impl.push]
  rw [Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_root 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push e comp noop act data lazy i).2.getD i noop = noop := by
  simp only [Impl.push]
  rw [Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_data_of_ne 
    {cap i j : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hleft : i * 2 ≠ j) (hright : i * 2 + 1 ≠ j) :
    (Impl.push e comp noop act data lazy i).1.getD j e = data.getD j e := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ hright,
    Impl.getD_setD_of_ne _ _ _ hleft]

private theorem Impl.push_lazy_left 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap) :
    (Impl.push e comp noop act data lazy i).2.getD (i * 2) noop =
      comp (lazy.getD i noop) (lazy.getD (i * 2) noop) := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_right 
    {cap i : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) :
    (Impl.push e comp noop act data lazy i).2.getD (i * 2 + 1) noop =
      comp (lazy.getD i noop) (lazy.getD (i * 2 + 1) noop) := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ (by omega),
    Impl.getD_setD_self _ _ _ (by omega)]

private theorem Impl.push_lazy_of_ne 
    {cap i j : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hleft : i * 2 ≠ j) (hright : i * 2 + 1 ≠ j) (hroot : i ≠ j) :
    (Impl.push e comp noop act data lazy i).2.getD j noop = lazy.getD j noop := by
  simp only [Impl.push]
  rw [Impl.getD_setD_of_ne _ _ _ hroot,
    Impl.getD_setD_of_ne _ _ _ hright,
    Impl.getD_setD_of_ne _ _ _ hleft]

private theorem Impl.push_internalAt [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap) (hvalid : internalAt op e comp noop act data lazy i) :
    let result := Impl.push e comp noop act data lazy i
    internalAt op e comp noop act result.1 result.2 i := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_root data lazy hi0, Impl.push_lazy_root data lazy hi,
    Impl.push_data_left data lazy hi, Impl.push_data_right data lazy hi]
  rw [actNoop op e comp noop act, ← actOp op e comp noop act]
  exact hvalid

private theorem Impl.push_internalAt_left [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i * 2 < cap)
    (hvalid : internalAt op e comp noop act data lazy (i * 2)) :
    let result := Impl.push e comp noop act data lazy i
    internalAt op e comp noop act result.1 result.2 (i * 2) := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_left data lazy (by omega),
    Impl.push_lazy_left data lazy hi0 (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    actComp op e comp noop act, hvalid, actOp op e comp noop act]

private theorem Impl.push_internalAt_right [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i * 2 + 1 < cap)
    (hvalid : internalAt op e comp noop act data lazy (i * 2 + 1)) :
    let result := Impl.push e comp noop act data lazy i
    internalAt op e comp noop act result.1 result.2 (i * 2 + 1) := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_right data lazy (by omega),
    Impl.push_lazy_right data lazy (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    actComp op e comp noop act, hvalid, actOp op e comp noop act]

private theorem Impl.push_internalAt_away [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hroot : j ≠ i) (hleft : j ≠ i * 2) (hright : j ≠ i * 2 + 1)
    (hvalid : internalAt op e comp noop act data lazy j) :
    let result := Impl.push e comp noop act data lazy i
    internalAt op e comp noop act result.1 result.2 j := by
  dsimp only
  unfold internalAt
  rw [Impl.push_data_of_ne data lazy hleft.symm hright.symm,
    Impl.push_lazy_of_ne data lazy hleft.symm hright.symm hroot.symm,
    Impl.push_data_of_ne data lazy (by omega) (by omega),
    Impl.push_data_of_ne data lazy (by omega) (by omega)]
  exact hvalid

private theorem Impl.push_internalValid [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi0 : i ≠ 0) (hi : i < cap)
    (hvalid : ∀ j, j ≠ 0 → j < cap → internalAt op e comp noop act data lazy j) :
    let result := Impl.push e comp noop act data lazy i
    ∀ j, j ≠ 0 → j < cap → internalAt op e comp noop act result.1 result.2 j := by
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

private theorem Impl.push_preserves_one [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i j : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (hi : i < cap) (hj : data.getD j e = e) :
    (Impl.push e comp noop act data lazy i).1.getD j e = e := by
  by_cases hjl : j = i * 2
  · subst j
    rw [Impl.push_data_left data lazy hi, hj, actE op e comp noop act]
  by_cases hjr : j = i * 2 + 1
  · subst j
    rw [Impl.push_data_right data lazy hi, hj, actE op e comp noop act]
  rw [Impl.push_data_of_ne data lazy (by omega) (by omega), hj]

/- During a recursive range update, only ancestors of the current subtree may
temporarily fail their node equation.  Parameterising the exceptional nodes
keeps that temporary state explicit. -/
private def internalValidOutside (op : M → M → M) (e : M) (comp : F → F → F) (noop : F)
    (act : F → M → M) {cap : Nat} (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) : Prop :=
  ∀ j, j ≠ 0 → j < cap → ¬ except j → internalAt op e comp noop act data lazy j

private theorem Impl.push_internalValidOutside [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) (hi0 : i ≠ 0) (hi : i < cap)
    (hvalid : internalValidOutside op e comp noop act data lazy except) :
    let result := Impl.push e comp noop act data lazy i
    internalValidOutside op e comp noop act result.1 result.2 except := by
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

private theorem Impl.applyNode_internalValidOutside [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) (f : F)
    (except : Nat → Prop) (hi0 : i ≠ 0)
    (hvalid : internalValidOutside op e comp noop act data lazy except) :
    let result := Impl.applyNode e comp noop act data lazy i f
    internalValidOutside op e comp noop act result.1 result.2
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

private theorem Impl.repair_internalValidOutside [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap i : Nat}
    (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2))
    (except : Nat → Prop) (hi : i < cap)
    (hlazy : lazy.getD i noop = noop)
    (hvalid : internalValidOutside op e comp noop act data lazy (fun j => except j ∨ j = i)) :
    internalValidOutside op e comp noop act
      (Impl.setD data i (op (data.getD (i * 2) e) (data.getD (i * 2 + 1) e))) lazy
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
    rw [hlazy, actNoop op e comp noop act]
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

private theorem Impl.applyRange_lazy_of_lt [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap : Nat} (f : F) (ql qr : Nat) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)) (j : Nat), j < i →
      (Impl.applyRange op e comp noop act f ql qr fuel i l r data lazy).2.getD j noop =
        lazy.getD j noop := by
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
        · let pushed := Impl.push e comp noop act data lazy i
          let mid := l + (r - l) / 2
          let left := Impl.applyRange op e comp noop act f ql qr fuel (i * 2) l mid
            pushed.1 pushed.2
          let right := Impl.applyRange op e comp noop act f ql qr fuel (i * 2 + 1) mid r
            left.1 left.2
          change right.2.getD j noop = lazy.getD j noop
          rw [ih (i * 2 + 1) mid r left.1 left.2 j (by omega),
            ih (i * 2) l mid pushed.1 pushed.2 j (by omega)]
          dsimp only [pushed]
          rw [Impl.push_lazy_of_ne data lazy (by omega) (by omega) (by omega)]

private theorem Impl.applyRange_internalValidOutside [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap : Nat} (f : F) (ql qr : Nat) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)) (except : Nat → Prop),
      i ≠ 0 → r ≤ cap → (r - l).isPowerOfTwo → i * (r - l) = cap + l →
      internalValidOutside op e comp noop act data lazy except →
      let result := Impl.applyRange op e comp noop act f ql qr fuel i l r data lazy
      internalValidOutside op e comp noop act result.1 result.2
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
              let pushed := Impl.push e comp noop act data lazy i
              have hvp : internalValidOutside op e comp noop act pushed.1 pushed.2 except :=
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
              let left := Impl.applyRange op e comp noop act f ql qr fuel (i * 2) l mid
                pushed.1 pushed.2
              have hvl : internalValidOutside op e comp noop act left.1 left.2
                  (fun j => except j ∨ j = i) := by
                simpa [left] using
                  ih (i * 2) l mid pushed.1 pushed.2 except (by omega)
                    (by omega) hleftPow hleftCap hvp
              let right := Impl.applyRange op e comp noop act f ql qr fuel (i * 2 + 1) mid r
                left.1 left.2
              have hvr : internalValidOutside op e comp noop act right.1 right.2
                  (fun j => except j ∨ j = i) := by
                have h := ih (i * 2 + 1) mid r left.1 left.2
                  (fun j => except j ∨ j = i) (by omega) hrcap hrightPow hrightCap hvl
                have hparent : (i * 2 + 1) / 2 = i := by omega
                simpa [right, hparent, or_assoc] using h
              change internalValidOutside op e comp noop act
                (Impl.setD right.1 i
                  (op (right.1.getD (i * 2) e) (right.1.getD (i * 2 + 1) e)))
                right.2 (fun j => except j ∨ j = i / 2)
              apply Impl.repair_internalValidOutside right.1 right.2 except hil
              · rw [Impl.applyRange_lazy_of_lt f ql qr fuel (i * 2 + 1) mid r
                    left.1 left.2 i (by omega),
                  Impl.applyRange_lazy_of_lt f ql qr fuel (i * 2) l mid
                    pushed.1 pushed.2 i (by omega)]
                exact Impl.push_lazy_root data lazy hil
              · exact hvr

private def paddingValid (e : M) {cap : Nat} (data : Vector M (cap * 2))
    (sz : Nat) : Prop :=
  ∀ x, sz ≤ x → x < cap → data.getD (cap + x) e = e

private theorem Impl.applyRange_paddingValid [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp] [Std.LawfulIdentity comp noop]
    [LawfulAct op e comp noop act] {cap sz : Nat} (f : F) (ql qr : Nat)
    (hqr : qr ≤ sz) :
    ∀ (fuel i l r : Nat) (data : Vector M (cap * 2))
      (lazy : Vector F (cap * 2)),
      i ≠ 0 → r ≤ cap → (r - l).isPowerOfTwo →
      i * (r - l) = cap + l → paddingValid e data sz →
      paddingValid e (Impl.applyRange op e comp noop act f ql qr fuel i l r data lazy).1 sz := by
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
              let pushed := Impl.push e comp noop act data lazy i
              have hpadPush : paddingValid e pushed.1 sz := by
                intro x hsx hx
                exact Impl.push_preserves_one (op := op) data lazy hil (hpadding x hsx hx)
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
              let left := Impl.applyRange op e comp noop act f ql qr fuel (i * 2) l mid
                pushed.1 pushed.2
              have hpadLeft : paddingValid e left.1 sz :=
                ih (i * 2) l mid pushed.1 pushed.2 (by omega) (by omega)
                  ⟨k, hml⟩ hleftCap hpadPush
              let right := Impl.applyRange op e comp noop act f ql qr fuel (i * 2 + 1) mid r
                left.1 left.2
              have hpadRight : paddingValid e right.1 sz :=
                ih (i * 2 + 1) mid r left.1 left.2 (by omega) hrcap
                  ⟨k, hrm⟩ hrightCap hpadLeft
              intro x hsx hx
              change (Impl.setD right.1 i
                (op (right.1.getD (i * 2) e) (right.1.getD (i * 2 + 1) e))).getD
                  (cap + x) e = e
              rw [Impl.getD_setD_of_ne _ _ _ (by omega)]
              exact hpadRight x hsx hx

@[simp] theorem ofArray_sz (xs : Array M) :
    (ofArray op e comp noop act xs).sz = xs.size := rfl

@[simp] theorem applyRange_sz 
    (self : LazySegTree M F op e comp noop act) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).sz = self.sz := rfl

@[simp] theorem applyRange_cap 
    (self : LazySegTree M F op e comp noop act) (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap = self.cap := rfl

@[simp] theorem applyRange_sz_le 
    (self : LazySegTree M F op e comp noop act)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).sz_le = self.sz_le := rfl

@[simp] theorem applyRange_cap_pos 
    (self : LazySegTree M F op e comp noop act)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap_pos = self.cap_pos := rfl

@[simp] theorem applyRange_cap_pow2 
    (self : LazySegTree M F op e comp noop act)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).cap_pow2 = self.cap_pow2 := rfl

/-- The representation invariant of a lazy segment tree.  An internal node stores
the action recorded at that node applied to the product of its children; unused
leaves contain the monoid identity. -/
def Valid [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (self : LazySegTree M F op e comp noop act) : Prop :=
  (∀ i : Fin self.cap, i.val ≠ 0 →
    self.data[i.val]'(by
      have hi := i.isLt
      have hc := self.cap_pos
      omega) =
      act (self.lazy[i.val]'(by
        have hi := i.isLt
        have hc := self.cap_pos
        omega))
        (op (self.data[i.val * 2]'(by
          have hi := i.isLt
          omega))
        (self.data[i.val * 2 + 1]'(by
          have hi := i.isLt
          omega)))) ∧
  (∀ i : Fin self.cap, self.sz ≤ i.val →
    self.data[self.cap + i.val]'(by
      have hi := i.isLt
      omega) = e)

theorem Valid.internalAt [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    {self : LazySegTree M F op e comp noop act} (hself : self.Valid)
    (i : Nat) (hi0 : i ≠ 0) (hi : i < self.cap) :
    internalAt op e comp noop act self.data self.lazy i := by
  have h := hself.1 ⟨i, hi⟩ hi0
  unfold LazySegTree.internalAt Vector.getD Array.getD
  simp only [Vector.size_toArray]
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega),
    dif_pos (by omega)]
  exact h

theorem Valid.padding [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    {self : LazySegTree M F op e comp noop act} (hself : self.Valid)
    (i : Nat) (hsi : self.sz ≤ i) (hi : i < self.cap) :
    self.data.getD (self.cap + i) e = e := by
  have h := hself.2 ⟨i, hi⟩ hsi
  unfold Vector.getD Array.getD
  simp only [Vector.size_toArray]
  rw [dif_pos (by omega)]
  exact h

/-- A lazy range update preserves the representation invariant. -/
theorem applyRange_Valid [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (self : LazySegTree M F op e comp noop act) (hself : self.Valid)
    (l r : Fin (self.sz + 1)) (f : F) :
    (self.applyRange l r f).Valid := by
  let result := Impl.applyRange op e comp noop act f l r self.cap 1 0 self.cap
    self.data self.lazy
  have hinternal : internalValidOutside op e comp noop act self.data self.lazy
      (fun _ => False) := by
    intro i hi0 hi _
    exact hself.internalAt i hi0 hi
  have hout := Impl.applyRange_internalValidOutside f l r self.cap 1 0 self.cap
    self.data self.lazy (fun _ => False) (by omega) (by omega)
    self.cap_pow2 (by simp) hinternal
  have hpadding : paddingValid e self.data self.sz := by
    intro i hsi hi
    exact hself.padding i hsi hi
  have hpadout := Impl.applyRange_paddingValid (op := op) (e := e) (comp := comp)
    (noop := noop) (act := act) f l r (by omega) self.cap 1 0 self.cap
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
theorem apply_Valid [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (self : LazySegTree M F op e comp noop act) (hself : self.Valid)
    (i : Fin self.sz) (f : F) : (self.apply i f).Valid := by
  unfold apply
  exact applyRange_Valid self hself _ _ f

theorem ofArray_Valid [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (xs : Array M) : Valid (ofArray op e comp noop act xs) := by
  have h := SegTree.ofArray_Valid op e xs
  constructor
  · intro i hi0
    simpa [ofArray, Valid, LawfulAct.act_noop (op := op) (e := e) (comp := comp) (noop := noop)
      (act := act)] using h.1 i hi0
  · intro i hi
    simpa [ofArray, Valid] using h.2 i hi

@[simp] theorem ofArray_lazy [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (xs : Array M) :
    (ofArray op e comp noop act xs).lazy =
      Vector.replicate (xs.size.nextPowerOfTwo * 2) noop := rfl

@[simp] theorem allProd_ofArray [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (xs : Array M) :
    (ofArray op e comp noop act xs).allProd = (SegTree.ofArray op e xs).allProd := rfl

theorem apply_eq_applyRange 
    (self : LazySegTree M F op e comp noop act) (i : Fin self.sz) (f : F) :
    self.apply i f = self.applyRange ⟨i, by omega⟩ ⟨i + 1, by omega⟩ f := rfl

private theorem Impl.prod_of_ge [Std.Associative op] [Std.LawfulIdentity op e]
    [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    {cap : Nat} (ql qr : Nat) (hqr : qr ≤ ql) (fuel i left right : Nat)
    (pending : F) (data : Vector M (cap * 2)) (lazy : Vector F (cap * 2)) :
    Impl.prod op e comp noop act ql qr fuel i left right pending data lazy = e := by
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
      · rw [ih, ih, Std.LawfulRightIdentity.right_id (op := op)]

@[simp] theorem prod_of_ge [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (self : LazySegTree M F op e comp noop act) (l r : Fin (self.sz + 1)) (h : r ≤ l) :
    self.prod l r = e := by
  exact Impl.prod_of_ge (op := op) (act := act) l r (by omega) self.cap 1 0 self.cap noop
    self.data self.lazy

@[simp] theorem prod_self [Std.Associative op] [Std.LawfulIdentity op e] [Std.Associative comp]
    [Std.LawfulIdentity comp noop] [LawfulAct op e comp noop act]
    (self : LazySegTree M F op e comp noop act) (i : Fin (self.sz + 1)) : self.prod i i = e :=
  prod_of_ge self i i (by rfl)

/-! ## Tests -/

/-- Range-add with range-sum, the standard example: a value is a running sum
alongside the length it covers, an action is the amount being added, and
neither needs a type of its own. This checks how stacked actions compose, how
overlapping updates interact, and that sub-range queries agree. -/
example :
    let op := fun x y : Nat × Nat => (x.1 + y.1, x.2 + y.2)
    let act := fun (f : Nat) (x : Nat × Nat) => (x.1 + f * x.2, x.2)
    let tree := ofArray op (0, 0) (· + ·) 0 act (#[1, 2, 3, 4, 5].map fun v => (v, 1))
    let tree := tree.applyRange 1 4 10
    let tree := tree.applyRange 2 5 3
    tree.prod 0 5 == (54, 5) && tree.prod 2 4 == (33, 2) &&
      tree.get ⟨2, by decide⟩ == (16, 1) && tree.allProd == (54, 5) &&
      tree.maxRight 0 (fun x => x.1 ≤ 30) == 3 &&
      tree.minLeft 5 (fun x => x.1 ≤ 30) == 3 &&
      tree.maxRight 1 (fun x => x.1 ≤ 28) == 3 &&
      tree.minLeft 4 (fun x => x.1 ≤ 33) == 2 := by
  native_decide

/-- Range-assign with range-max, on the same tree type: an action is `none` for
"leave alone" and `some v` for "make everything `v`". -/
example :
    let act := fun (f : Option Nat) (x : Nat) => f.getD x
    let comp := fun (f g : Option Nat) => f.or g
    let tree := ofArray Nat.max 0 comp none act #[3, 1, 4, 1, 5]
    let tree := tree.applyRange 1 3 (some 9)
    tree.prod 0 5 == 9 && tree.prod 3 5 == 5 && tree.get ⟨1, by decide⟩ == 9 &&
      tree.get ⟨3, by decide⟩ == 1 := by
  native_decide

end LazySegTree

end Cplib
