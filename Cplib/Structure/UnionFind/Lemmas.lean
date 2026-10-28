import Cplib.Structure.UnionFind.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

namespace Cplib

/-!
# Structure.UnionFind.Lemmas

Specification of the union-find in `Structure.UnionFind.Basic`.

`Valid` is the invariant every state this API produces, and `empty`, `merge` and
`persistentMerge` all keep it. It has two halves. `Ordered` says sizes rise
along every parent edge, which is what makes a representative meaningful: a walk
that cannot revisit a vertex reaches a root in fewer than `n` steps. On top of
that, the size recorded at a root counts the vertices that root represents, so
`size` and `persistentSize` report the number of vertices in the component
rather than a number the structure merely carried.

The two families of operations are related here rather than specified twice.
`leader`, `same`, `size` and `merge` answer exactly what `persistentLeader`,
`persistentSame`, `persistentSize` and `persistentMerge` answer, and the state
they hand back has the same representatives as the one they were given. Path
compression is an optimisation that cannot be observed through the API.
-/

namespace UnionFind

variable {n : Nat}

namespace Impl

/-- The vertex reached by following `parent` `k` times. -/
def iter (self : UnionFind n) : Nat → Fin n → Fin n
  | 0, a => a
  | k + 1, a => self.parent[iter self k a]

@[simp] theorem iter_zero (self : UnionFind n) (a : Fin n) : iter self 0 a = a := rfl

@[simp] theorem iter_succ (self : UnionFind n) (k : Nat) (a : Fin n) :
    iter self (k + 1) a = self.parent[iter self k a] := rfl

theorem iter_succ_left (self : UnionFind n) (k : Nat) (a : Fin n) :
    iter self k self.parent[a] = iter self (k + 1) a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show self.parent[iter self k self.parent[a]] = self.parent[iter self (k + 1) a]
      rw [ih]

theorem persistentLeaderFuel_succ_of_eq (self : UnionFind n) (a : Fin n) (k : Nat)
    (hp : self.parent[a] = a) : persistentLeaderFuel (k + 1) self a = a := by
  show (if self.parent[a] = a then a else persistentLeaderFuel k self self.parent[a]) = _
  rw [if_pos hp]

theorem persistentLeaderFuel_succ_of_ne (self : UnionFind n) (a : Fin n) (k : Nat)
    (hp : self.parent[a] ≠ a) :
    persistentLeaderFuel (k + 1) self a = persistentLeaderFuel k self self.parent[a] := by
  show (if self.parent[a] = a then a else persistentLeaderFuel k self self.parent[a]) = _
  rw [if_neg hp]

/-- Walking with `fuel` steps lands on the first root along the path, as soon as
the fuel reaches it. -/
theorem persistentLeaderFuel_eq_iter (self : UnionFind n) (a : Fin n) (j fuel : Nat)
    (hj : j ≤ fuel)
    (hfix : self.parent[iter self j a] = iter self j a)
    (hmin : ∀ i, i < j → self.parent[iter self i a] ≠ iter self i a) :
    persistentLeaderFuel fuel self a = iter self j a := by
  induction fuel generalizing a j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      rfl
  | succ fuel ih =>
      by_cases hp : self.parent[a] = a
      · have hj0 : j = 0 := by
          by_contra hne
          exact hmin 0 (by omega) (by simpa using hp)
        subst hj0
        rw [persistentLeaderFuel_succ_of_eq self a fuel hp]
        rfl
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
          cases j with
          | zero => exact absurd (by simpa using hfix) hp
          | succ j' => exact ⟨j', rfl⟩
        rw [persistentLeaderFuel_succ_of_ne self a fuel hp, ← iter_succ_left]
        refine ih self.parent[a] j' (by omega) ?_ ?_
        · rw [iter_succ_left]; exact hfix
        · intro i hi
          rw [iter_succ_left]
          exact hmin (i + 1) (by omega)

end Impl

/-- A root is its own representative, whatever shape the rest is in. -/
theorem persistentLeader_eq_self (self : UnionFind n) {a : Fin n} (ha : self.parent[a] = a) :
    self.persistentLeader a = a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
  have hfuel : self.persistentLeader a = Impl.persistentLeaderFuel (n - 1 + 1) self a := by
    show Impl.persistentLeaderFuel n self a = _
    congr 1
    omega
  rw [hfuel, Impl.persistentLeaderFuel_succ_of_eq self a (n - 1) ha]

/-- Every non-root sits below a vertex of strictly greater recorded size.

Union by size keeps this: the root that loses a merge keeps the size it had,
while the one that wins takes the sum. Sizes therefore rise along every parent
edge, so no path can visit a vertex twice, and a walk reaches a root in fewer
than `n` steps. -/
structure Ordered (uf : UnionFind n) : Prop where
  size_pos : ∀ a : Fin n, 0 < uf.componentSize[a]
  size_lt : ∀ a : Fin n, uf.parent[a] ≠ a →
    uf.componentSize[a] < uf.componentSize[uf.parent[a]]

namespace Ordered
variable {self : UnionFind n}

/-- Along a path that has not reached a root, sizes strictly rise. -/
private theorem size_iter_lt (h : self.Ordered) (a : Fin n) (k : Nat)
    (hk : ∀ i, i < k → self.parent[Impl.iter self i a] ≠ Impl.iter self i a) :
    ∀ i j, i < j → j ≤ k →
      self.componentSize[Impl.iter self i a] < self.componentSize[Impl.iter self j a] := by
  intro i j hij hjk
  induction j with
  | zero => omega
  | succ j ih =>
      have hstep : self.componentSize[Impl.iter self j a] <
          self.componentSize[Impl.iter self (j + 1) a] := by
        rw [Impl.iter_succ]
        exact h.size_lt _ (hk j (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | heq
      · exact Nat.lt_trans (ih hlt (by omega)) hstep
      · subst heq
        exact hstep

/-- A walk reaches a root in fewer than `n` steps: sizes rise along it, so it
cannot visit a vertex twice, and there are only `n` to visit. -/
theorem exists_fix (h : self.Ordered) (a : Fin n) :
    ∃ j, j < n ∧ self.parent[Impl.iter self j a] = Impl.iter self j a := by
  by_contra hc
  push_neg at hc
  have hmono := size_iter_lt h a n (fun i hi => hc i hi)
  have hinj : Function.Injective (fun k : Fin (n + 1) => Impl.iter self k.val a) := by
    intro p q hpq
    by_contra hne
    have hne' : p.val ≠ q.val := fun hv => hne (Fin.ext hv)
    rcases Nat.lt_or_ge p.val q.val with hlt | hge
    · exact absurd (congrArg (fun v => self.componentSize[v]) hpq)
        (Nat.ne_of_lt (hmono p.val q.val hlt (by omega)))
    · have hlt : q.val < p.val := by omega
      exact absurd (congrArg (fun v => self.componentSize[v]) hpq.symm)
        (Nat.ne_of_lt (hmono q.val p.val hlt (by omega)))
  have := Fintype.card_le_of_injective _ hinj
  simp at this

/-- The first root along the walk from `a`, reached in fewer than `n` steps. -/
theorem exists_least_fix (h : self.Ordered) (a : Fin n) :
    ∃ j, j < n ∧ self.parent[Impl.iter self j a] = Impl.iter self j a ∧
      ∀ i, i < j → self.parent[Impl.iter self i a] ≠ Impl.iter self i a := by
  obtain ⟨j, hjn, hj⟩ := h.exists_fix a
  classical
  have hex : ∃ j, self.parent[Impl.iter self j a] = Impl.iter self j a := ⟨j, hj⟩
  exact ⟨Nat.find hex, Nat.lt_of_le_of_lt (Nat.find_le hj) hjn, Nat.find_spec hex,
    fun i hi => Nat.find_min hex hi⟩

/-- `persistentLeader` is what the walk arrives at. -/
theorem persistentLeader_eq_iter (h : self.Ordered) (a : Fin n) :
    ∃ j, j < n ∧ self.persistentLeader a = Impl.iter self j a ∧
      self.parent[Impl.iter self j a] = Impl.iter self j a := by
  obtain ⟨j, hjn, hfix, hmin⟩ := h.exists_least_fix a
  refine ⟨j, hjn, ?_, hfix⟩
  show Impl.persistentLeaderFuel n self a = _
  exact Impl.persistentLeaderFuel_eq_iter self a j n (by omega) hfix hmin

/-- Any fuel from `n - 1` on computes `persistentLeader`: no walk is longer. -/
theorem persistentLeaderFuel_eq (h : self.Ordered) (a : Fin n) (k : Nat) (hk : n - 1 ≤ k) :
    Impl.persistentLeaderFuel k self a = self.persistentLeader a := by
  obtain ⟨j, hjn, hfix, hmin⟩ := h.exists_least_fix a
  rw [Impl.persistentLeaderFuel_eq_iter self a j k (by omega) hfix hmin]
  show _ = Impl.persistentLeaderFuel n self a
  rw [Impl.persistentLeaderFuel_eq_iter self a j n (by omega) hfix hmin]

/-- `persistentLeader` lands on a root. -/
@[simp] theorem parent_persistentLeader (h : self.Ordered) (a : Fin n) :
    self.parent[self.persistentLeader a] = self.persistentLeader a := by
  obtain ⟨j, _, heq, hfix⟩ := h.persistentLeader_eq_iter a
  rw [heq]
  exact hfix

/-- Stepping to the parent does not change the representative. -/
theorem persistentLeader_parent (h : self.Ordered) (a : Fin n) :
    self.persistentLeader self.parent[a] = self.persistentLeader a := by
  by_cases hp : self.parent[a] = a
  · rw [hp]
  · have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
    have hfuel : self.persistentLeader a = Impl.persistentLeaderFuel (n - 1 + 1) self a := by
      show Impl.persistentLeaderFuel n self a = _
      congr 1
      omega
    rw [hfuel, Impl.persistentLeaderFuel_succ_of_ne self a (n - 1) hp,
      h.persistentLeaderFuel_eq self.parent[a] (n - 1) (le_refl _)]

@[simp] theorem persistentLeader_idem (h : self.Ordered) (a : Fin n) :
    self.persistentLeader (self.persistentLeader a) = self.persistentLeader a :=
  persistentLeader_eq_self self (h.parent_persistentLeader a)

/-- Induction by walking to the root: prove it of every root, and of `a` given
it for `a`'s parent. -/
theorem parent_induction (h : self.Ordered) {motive : Fin n → Prop}
    (base : ∀ a, self.parent[a] = a → motive a)
    (step : ∀ a, self.parent[a] ≠ a → motive self.parent[a] → motive a)
    (a : Fin n) : motive a := by
  have key : ∀ j (a : Fin n), self.parent[Impl.iter self j a] = Impl.iter self j a → motive a := by
    intro j
    induction j with
    | zero => intro a ha; exact base a (by simpa using ha)
    | succ j ih =>
        intro a ha
        by_cases hp : self.parent[a] = a
        · exact base a hp
        · refine step a hp (ih self.parent[a] ?_)
          rw [Impl.iter_succ_left]
          exact ha
  obtain ⟨j, _, hfix, _⟩ := h.exists_least_fix a
  exact key j a hfix

/-- Sizes do not fall on the way to the root. -/
theorem size_le_size_persistentLeader (h : self.Ordered) (a : Fin n) :
    self.componentSize[a] ≤ self.componentSize[self.persistentLeader a] := by
  induction a using h.parent_induction with
  | base a ha => rw [persistentLeader_eq_self self ha]
  | step a ha ih =>
      rw [← h.persistentLeader_parent a]
      exact Nat.le_trans (Nat.le_of_lt (h.size_lt a ha)) ih

end Ordered

@[simp] theorem empty_persistentLeader {n : Nat} (i : Fin n) :
    (empty n).persistentLeader i = i :=
  persistentLeader_eq_self _ (by simp [empty])

/-- The vertices `r` represents: those whose walk up the parents ends at `r`.

Only the roots represent anything: in an `Ordered` state `persistentLeader`
lands on a root, so the component of a non-root is empty. -/
def component (self : UnionFind n) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => self.persistentLeader v = r

@[simp] theorem mem_component {self : UnionFind n} {r v : Fin n} :
    v ∈ self.component r ↔ self.persistentLeader v = r := by
  simp [component]

/-- The invariant every state this API produces.

`Ordered` is the half that makes a representative meaningful. On top of it, the
size recorded at a root is the number of vertices that root represents, which is
what makes `size` and `persistentSize` answer the question they claim to.

Union by size keeps the count: a link adds the two sizes, and the two components
it joins are disjoint, so the sum is the size of the component that comes out.
Path compression moves no vertex between components and touches no size. -/
structure Valid (uf : UnionFind n) : Prop extends Ordered uf where
  size_eq_card : ∀ r : Fin n, uf.parent[r] = r →
    uf.componentSize[r] = (uf.component r).card

@[simp] theorem empty_Valid (n : Nat) : (empty n).Valid where
  size_pos a := by simp [empty]
  size_lt a ha := absurd (by simp [empty]) ha
  size_eq_card r _ := by
    have hcomp : (empty n).component r = {r} := by
      ext v
      simp
    rw [hcomp, Finset.card_singleton]
    simp [empty]

namespace Impl

/-- The structure `link` builds when it hangs the root `x` under the root `y`. -/
def attach (self : UnionFind n) (x y : Fin n) (s : Nat) : UnionFind n :=
  ⟨self.parent.set x y, self.componentSize.set y s⟩

@[simp] theorem attach_parent (self : UnionFind n) (x y : Fin n) (s : Nat) (c : Fin n) :
    (attach self x y s).parent[c] = if x = c then y else self.parent[c] := by
  simp [attach, Vector.getElem_set, Fin.val_inj]

@[simp] theorem attach_componentSize (self : UnionFind n) (x y : Fin n) (s : Nat) (c : Fin n) :
    (attach self x y s).componentSize[c] = if y = c then s else self.componentSize[c] := by
  simp [attach, Vector.getElem_set, Fin.val_inj]

/-- Hanging a root under a root of at least its size keeps the order. -/
theorem attach_Ordered {self : UnionFind n} (h : self.Ordered) {x y : Fin n} {s : Nat}
    (hy : self.parent[y] = y) (hxy : x ≠ y)
    (hsx : self.componentSize[x] < s) (hsy : self.componentSize[y] ≤ s) :
    (attach self x y s).Ordered where
  size_pos c := by
    rw [attach_componentSize]
    split
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hsx
    · exact h.size_pos c
  size_lt c hc := by
    rw [attach_parent] at hc ⊢
    rw [attach_componentSize, attach_componentSize]
    by_cases hcx : x = c
    · subst hcx
      rw [if_pos rfl, if_neg (Ne.symm hxy), if_pos rfl]
      exact hsx
    · rw [if_neg hcx] at hc ⊢
      by_cases hcy : y = c
      · subst hcy
        exact absurd hy hc
      · rw [if_neg hcy]
        have hlt := h.size_lt c hc
        by_cases hpy : y = self.parent[c]
        · rw [if_pos hpy]
          rw [← hpy] at hlt
          omega
        · rw [if_neg hpy]
          exact hlt

/-- …and it sends exactly `x`'s component to `y`, leaving every other
representative alone. -/
theorem attach_persistentLeader {self : UnionFind n} (h : self.Ordered) {x y : Fin n} {s : Nat}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) (hxy : x ≠ y)
    (h' : (attach self x y s).Ordered) (c : Fin n) :
    (attach self x y s).persistentLeader c =
      if self.persistentLeader c = x then y else self.persistentLeader c := by
  induction c using h.parent_induction with
  | base c hc =>
      rw [persistentLeader_eq_self self hc]
      by_cases hcx : c = x
      · subst hcx
        rw [if_pos rfl, ← h'.persistentLeader_parent c, attach_parent, if_pos rfl,
          persistentLeader_eq_self _ (by rw [attach_parent, if_neg hxy]; exact hy)]
      · rw [if_neg hcx,
          persistentLeader_eq_self _ (by rw [attach_parent, if_neg (Ne.symm hcx)]; exact hc)]
  | step c hc ih =>
      have hcx : c ≠ x := fun hh => hc (hh ▸ hx)
      rw [← h'.persistentLeader_parent c, attach_parent, if_neg (Ne.symm hcx), ih,
        h.persistentLeader_parent c]


/-- …so the component of `y` takes in the whole component of `x`, and no other
component changes. -/
theorem attach_component {self : UnionFind n} (h : self.Ordered) {x y : Fin n} {s : Nat}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) (hxy : x ≠ y)
    (h' : (attach self x y s).Ordered) {r : Fin n} (hrx : r ≠ x) :
    (attach self x y s).component r =
      if r = y then self.component x ∪ self.component y else self.component r := by
  ext v
  simp only [mem_component, attach_persistentLeader h hx hy hxy h' v]
  by_cases hry : r = y
  · subst hry
    by_cases hv : self.persistentLeader v = x <;> simp [hv]
  · simp only [if_neg hry]
    by_cases hv : self.persistentLeader v = x
    · simp [hv, Ne.symm hry, Ne.symm hrx]
    · simp [hv]

/-- Hanging a root under a root keeps the invariant: the component that comes
out holds the vertices of both the ones that went in, and they are disjoint, so
the sum of their sizes counts it. -/
theorem attach_Valid {self : UnionFind n} (h : self.Valid) {x y : Fin n}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) (hxy : x ≠ y) :
    (attach self x y (self.componentSize[x] + self.componentSize[y])).Valid := by
  have hord : (attach self x y (self.componentSize[x] + self.componentSize[y])).Ordered :=
    attach_Ordered h.toOrdered hy hxy (by have := h.size_pos y; omega) (by omega)
  refine ⟨hord, fun r hr => ?_⟩
  rw [attach_parent] at hr
  have hrx : r ≠ x := by
    rintro rfl
    rw [if_pos rfl] at hr
    exact hxy hr.symm
  rw [if_neg fun hh => hrx hh.symm] at hr
  rw [attach_componentSize, attach_component h.toOrdered hx hy hxy hord hrx]
  by_cases hry : r = y
  · have hdisj : Disjoint (self.component x) (self.component y) := by
      rw [Finset.disjoint_left]
      intro v hvx hvy
      simp only [mem_component] at hvx hvy
      exact hxy (hvx.symm.trans hvy)
    rw [if_pos hry.symm, if_pos hry, Finset.card_union_of_disjoint hdisj,
      ← h.size_eq_card x hx, ← h.size_eq_card y hy]
  · rw [if_neg fun hh => hry hh.symm, if_neg hry, h.size_eq_card r hr]

theorem link_eq_attach (self : UnionFind n) {x y : Fin n} (hxy : x ≠ y) :
    link self x y = if self.componentSize[x] < self.componentSize[y]
      then attach self x y (self.componentSize[x] + self.componentSize[y])
      else attach self y x (self.componentSize[x] + self.componentSize[y]) := by
  rw [link.eq_def, if_neg hxy]
  split <;> rfl

/-- Linking two roots keeps the order. -/
theorem link_Ordered {self : UnionFind n} (h : self.Ordered) {x y : Fin n}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) : (link self x y).Ordered := by
  by_cases hxy : x = y
  · rw [link.eq_def, if_pos hxy]
    exact h
  · rw [link_eq_attach self hxy]
    split
    · exact attach_Ordered h hy hxy (by have := h.size_pos y; omega) (by omega)
    · exact attach_Ordered h hx (Ne.symm hxy) (by have := h.size_pos x; omega) (by omega)

/-- Linking two roots keeps the invariant, counting included. -/
theorem link_Valid {self : UnionFind n} (h : self.Valid) {x y : Fin n}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) : (link self x y).Valid := by
  by_cases hxy : x = y
  · rw [link.eq_def, if_pos hxy]
    exact h
  · rw [link_eq_attach self hxy]
    split
    · exact attach_Valid h hx hy hxy
    · rw [Nat.add_comm self.componentSize[x] self.componentSize[y]]
      exact attach_Valid h hy hx (Ne.symm hxy)

/-- Linking two roots merges exactly their two components, and leaves every other
representative where it was. -/
theorem link_persistentLeader {self : UnionFind n} (h : self.Ordered) {x y : Fin n}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) :
    ∃ w, (w = x ∨ w = y) ∧ ∀ c, (link self x y).persistentLeader c =
      if self.persistentLeader c = x ∨ self.persistentLeader c = y then w
      else self.persistentLeader c := by
  by_cases hxy : x = y
  · subst hxy
    refine ⟨x, Or.inl rfl, fun c => ?_⟩
    rw [link.eq_def, if_pos rfl]
    split <;> simp_all
  · have hlink := link_eq_attach self hxy
    by_cases hlt : self.componentSize[x] < self.componentSize[y]
    · refine ⟨y, Or.inr rfl, fun c => ?_⟩
      rw [hlink, if_pos hlt,
        attach_persistentLeader h hx hy hxy
          (attach_Ordered h hy hxy (by have := h.size_pos y; omega) (by omega)) c]
      by_cases hc : self.persistentLeader c = x
      · simp [hc]
      · by_cases hc' : self.persistentLeader c = y <;> simp [hc, hc']
    · refine ⟨x, Or.inl rfl, fun c => ?_⟩
      rw [hlink, if_neg hlt,
        attach_persistentLeader h hy hx (Ne.symm hxy)
          (attach_Ordered h hx (Ne.symm hxy) (by have := h.size_pos x; omega) (by omega)) c]
      by_cases hc : self.persistentLeader c = y
      · simp [hc]
      · by_cases hc' : self.persistentLeader c = x <;> simp [hc, hc']

/-- Two vertices come out connected after a link exactly when they already were,
or when one sits on each side of it. -/
theorem link_persistentLeader_eq {self : UnionFind n} (h : self.Ordered) {x y : Fin n}
    (hx : self.parent[x] = x) (hy : self.parent[y] = y) (c d : Fin n) :
    (link self x y).persistentLeader c = (link self x y).persistentLeader d ↔
      self.persistentLeader c = self.persistentLeader d ∨
        (self.persistentLeader c = x ∧ self.persistentLeader d = y) ∨
        (self.persistentLeader c = y ∧ self.persistentLeader d = x) := by
  obtain ⟨w, hw, hall⟩ := link_persistentLeader h hx hy
  rw [hall c, hall d]
  by_cases hcx : self.persistentLeader c = x <;>
    by_cases hcy : self.persistentLeader c = y <;>
    by_cases hdx : self.persistentLeader d = x <;>
    by_cases hdy : self.persistentLeader d = y <;>
    rcases hw with rfl | rfl <;> simp_all <;> grind

end Impl

namespace Ordered
variable {self : UnionFind n}

/-- Sizes strictly rise from a non-root to its representative. -/
theorem size_lt_size_persistentLeader (h : self.Ordered) {a : Fin n} (ha : self.parent[a] ≠ a) :
    self.componentSize[a] < self.componentSize[self.persistentLeader a] := by
  rw [← h.persistentLeader_parent a]
  exact Nat.lt_of_lt_of_le (h.size_lt a ha) (h.size_le_size_persistentLeader _)

end Ordered

namespace Impl

/-- The structure path compression builds when it points `a` straight at its
representative. -/
def compress (self : UnionFind n) (a : Fin n) (r : Fin n) : UnionFind n :=
  ⟨self.parent.set a r, self.componentSize⟩

@[simp] theorem compress_parent (self : UnionFind n) (a r c : Fin n) :
    (compress self a r).parent[c] = if a = c then r else self.parent[c] := by
  simp [compress, Vector.getElem_set, Fin.val_inj]

@[simp] theorem compress_componentSize (self : UnionFind n) (a r c : Fin n) :
    (compress self a r).componentSize[c] = self.componentSize[c] := rfl

/-- Pointing a vertex straight at its representative keeps the order: the
representative is where the sizes along the path end up. -/
theorem compress_Ordered {self : UnionFind n} (h : self.Ordered) (a : Fin n) :
    (compress self a (self.persistentLeader a)).Ordered where
  size_pos c := h.size_pos c
  size_lt c hc := by
    rw [compress_parent] at hc
    rw [compress_parent, compress_componentSize, compress_componentSize]
    by_cases hac : a = c
    · subst hac
      rw [if_pos rfl] at hc ⊢
      refine h.size_lt_size_persistentLeader (fun hh => hc ?_)
      rw [persistentLeader_eq_self self hh]
    · rw [if_neg hac] at hc ⊢
      exact h.size_lt c hc

/-- …and it changes no representative. -/
theorem compress_persistentLeader {self : UnionFind n} (h : self.Ordered) (a : Fin n) (c : Fin n) :
    (compress self a (self.persistentLeader a)).persistentLeader c = self.persistentLeader c := by
  have h' := compress_Ordered h a
  have hroot : ∀ b : Fin n, self.parent[b] = b →
      (compress self a (self.persistentLeader a)).parent[b] = b := by
    intro b hb
    rw [compress_parent]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, persistentLeader_eq_self self hb]
    · rw [if_neg hab]
      exact hb
  induction c using h.parent_induction with
  | base c hc =>
      rw [persistentLeader_eq_self self hc, persistentLeader_eq_self _ (hroot c hc)]
  | step c hc ih =>
      rw [← h'.persistentLeader_parent c, compress_parent]
      by_cases hac : a = c
      · subst hac
        rw [if_pos rfl,
          persistentLeader_eq_self _ (hroot _ (h.parent_persistentLeader a))]
      · rw [if_neg hac, ih, h.persistentLeader_parent c]

/-- Compression keeps the invariant: it moves no vertex between components and
leaves every size where it was. -/
theorem compress_Valid {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (compress self a (self.persistentLeader a)).Valid := by
  refine ⟨compress_Ordered h.toOrdered a, fun r hr => ?_⟩
  rw [compress_parent] at hr
  have hroot : self.parent[r] = r := by
    by_cases har : a = r
    · subst har
      rw [if_pos rfl] at hr
      have hpl := h.parent_persistentLeader a
      rwa [hr] at hpl
    · rwa [if_neg har] at hr
  rw [compress_componentSize, h.size_eq_card r hroot]
  congr 1
  ext v
  simp [compress_persistentLeader h.toOrdered a v]

theorem leaderFuel_succ_of_eq (self : UnionFind n) (a : Fin n) (fuel : Nat)
    (hp : self.parent[a] = a) : leaderFuel (fuel + 1) self a = (a, self) := by
  show (if self.parent[a] = a then (a, self) else _) = _
  rw [if_pos hp]

theorem leaderFuel_succ_of_ne (self : UnionFind n) (a : Fin n) (fuel : Nat)
    (hp : self.parent[a] ≠ a) :
    leaderFuel (fuel + 1) self a =
      ((leaderFuel fuel self self.parent[a]).1,
        compress (leaderFuel fuel self self.parent[a]).2 a
          (leaderFuel fuel self self.parent[a]).1) := by
  show (if self.parent[a] = a then (a, self) else _) = _
  rw [if_neg hp]
  rfl

/-- Path compression answers with the representative, keeps the invariant, and
leaves every representative where it was. -/
theorem leaderFuel_spec {self : UnionFind n} (h : self.Valid) (fuel : Nat) (a : Fin n)
    (hfuel : persistentLeaderFuel fuel self a = self.persistentLeader a) :
    (leaderFuel fuel self a).1 = self.persistentLeader a ∧
      (leaderFuel fuel self a).2.Valid ∧
      ∀ c, (leaderFuel fuel self a).2.persistentLeader c = self.persistentLeader c := by
  induction fuel generalizing self a with
  | zero => exact ⟨hfuel, h, fun _ => rfl⟩
  | succ fuel ih =>
      by_cases hp : self.parent[a] = a
      · rw [leaderFuel_succ_of_eq self a fuel hp]
        exact ⟨(persistentLeader_eq_self self hp).symm, h, fun _ => rfl⟩
      · have hstep : persistentLeaderFuel fuel self self.parent[a] =
            self.persistentLeader self.parent[a] := by
          rw [h.persistentLeader_parent a, ← hfuel,
            persistentLeaderFuel_succ_of_ne self a fuel hp]
        obtain ⟨h1, h2, h3⟩ := ih h self.parent[a] hstep
        rw [h.persistentLeader_parent a] at h1
        have hval : (leaderFuel fuel self self.parent[a]).1 =
            (leaderFuel fuel self self.parent[a]).2.persistentLeader a := by
          rw [h3 a, h1]
        rw [leaderFuel_succ_of_ne self a fuel hp]
        dsimp only
        refine ⟨h1, ?_, ?_⟩
        · rw [hval]
          exact compress_Valid h2 a
        · intro c
          rw [hval, compress_persistentLeader h2.toOrdered a c]
          exact h3 c

end Impl

/-! ## The persistent family -/

theorem persistentSame_iff (self : UnionFind n) (a b : Fin n) :
    self.persistentSame a b ↔ self.persistentLeader a = self.persistentLeader b := by
  simp [persistentSame]

@[simp] theorem persistentSame_self (self : UnionFind n) (a : Fin n) :
    self.persistentSame a a := by simp [persistentSame]

theorem persistentSame_comm (self : UnionFind n) (a b : Fin n) :
    self.persistentSame a b = self.persistentSame b a := by
  simp [persistentSame, BEq.comm]

theorem persistentSame_trans {self : UnionFind n} {a b c : Fin n}
    (hab : self.persistentSame a b) (hbc : self.persistentSame b c) :
    self.persistentSame a c := by
  rw [persistentSame_iff] at *
  exact hab.trans hbc

theorem persistentSize_eq (self : UnionFind n) (a : Fin n) :
    self.persistentSize a = self.componentSize[self.persistentLeader a] := rfl

/-- The component `a` belongs to is the set of vertices connected to `a`. -/
theorem component_persistentLeader (self : UnionFind n) (a : Fin n) :
    self.component (self.persistentLeader a) =
      Finset.univ.filter fun v => self.persistentSame v a := by
  ext v
  simp [persistentSame_iff]

/-- `persistentSize a` is the number of vertices connected to `a`, and not merely
the number the structure happens to carry. -/
theorem persistentSize_eq_card {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    self.persistentSize a = (Finset.univ.filter fun v => self.persistentSame v a).card := by
  rw [persistentSize_eq, h.size_eq_card _ (h.parent_persistentLeader a),
    component_persistentLeader self a]

/-- A component holds at most every vertex. -/
theorem persistentSize_le {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    self.persistentSize a ≤ n := by
  rw [persistentSize_eq_card h]
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
    fun v => self.persistentSame v a

@[simp] theorem empty_persistentSame {n : Nat} (i j : Fin n) :
    (empty n).persistentSame i j = (i == j) := by simp [persistentSame]

@[simp] theorem empty_persistentSize {n : Nat} (i : Fin n) :
    (empty n).persistentSize i = 1 := by simp [persistentSize, empty]

/-- `persistentMerge` keeps the invariant. -/
theorem persistentMerge_Valid {self : UnionFind n} (h : self.Valid) (a b : Fin n) :
    (self.persistentMerge a b).Valid :=
  Impl.link_Valid h (h.parent_persistentLeader a) (h.parent_persistentLeader b)

/-- `persistentMerge` joins the components of `a` and `b` and touches no others:
two vertices end up connected exactly when they already were, or when one sits
on each side of the merge. -/
theorem persistentMerge_persistentSame {self : UnionFind n} (h : self.Valid) (a b c d : Fin n) :
    (self.persistentMerge a b).persistentSame c d ↔
      self.persistentSame c d ∨
        (self.persistentSame c a ∧ self.persistentSame d b) ∨
        (self.persistentSame c b ∧ self.persistentSame d a) := by
  simp only [persistentSame_iff, persistentMerge]
  exact Impl.link_persistentLeader_eq h.toOrdered (h.parent_persistentLeader a)
    (h.parent_persistentLeader b) c d

/-- After `persistentMerge a b`, the two are connected. -/
@[simp] theorem persistentSame_persistentMerge {self : UnionFind n} (h : self.Valid) (a b : Fin n) :
    (self.persistentMerge a b).persistentSame a b :=
  (persistentMerge_persistentSame h a b a b).mpr
    (Or.inr (Or.inl ⟨persistentSame_self self a, persistentSame_self self b⟩))

/-- `persistentMerge` never separates vertices that were connected. -/
theorem persistentSame_of_persistentSame {self : UnionFind n} (h : self.Valid) {c d : Fin n}
    (a b : Fin n) (hcd : self.persistentSame c d) :
    (self.persistentMerge a b).persistentSame c d :=
  (persistentMerge_persistentSame h a b c d).mpr (Or.inl hcd)

/-- Merging two components that were apart adds their sizes. -/
theorem persistentSize_persistentMerge {self : UnionFind n} (h : self.Valid) {a b : Fin n}
    (hab : ¬ self.persistentSame a b) :
    (self.persistentMerge a b).persistentSize a =
      self.persistentSize a + self.persistentSize b := by
  have hdisj : Disjoint (Finset.univ.filter fun v => self.persistentSame v a)
      (Finset.univ.filter fun v => self.persistentSame v b) := by
    rw [Finset.disjoint_left]
    intro v hva hvb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hva hvb
    exact hab (persistentSame_trans ((persistentSame_comm self v a) ▸ hva) hvb)
  have hset : (Finset.univ.filter fun v => (self.persistentMerge a b).persistentSame v a) =
      (Finset.univ.filter fun v => self.persistentSame v a) ∪
        Finset.univ.filter fun v => self.persistentSame v b := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
      persistentMerge_persistentSame h a b v a]
    constructor
    · rintro (hv | ⟨_, hab'⟩ | ⟨hv, _⟩)
      · exact Or.inl hv
      · exact absurd hab' hab
      · exact Or.inr hv
    · rintro (hv | hv)
      · exact Or.inl hv
      · exact Or.inr (Or.inr ⟨hv, persistentSame_self self a⟩)
  rw [persistentSize_eq_card (persistentMerge_Valid h a b) a, hset,
    Finset.card_union_of_disjoint hdisj, persistentSize_eq_card h a, persistentSize_eq_card h b]

/-! ## The compressing family

Each operation answers exactly what its persistent counterpart answers, and the
state it hands back has the same representatives as the one it was given. -/

theorem Impl.leaderFuel_componentSize (fuel : Nat) (self : UnionFind n) (a : Fin n) :
    (Impl.leaderFuel fuel self a).2.componentSize = self.componentSize := by
  induction fuel generalizing self a with
  | zero => rfl
  | succ fuel ih =>
      by_cases hp : self.parent[a] = a
      · rw [Impl.leaderFuel_succ_of_eq self a fuel hp]
      · rw [Impl.leaderFuel_succ_of_ne self a fuel hp]
        exact ih self self.parent[a]

@[simp] theorem leader_componentSize (self : UnionFind n) (a : Fin n) :
    (self.leader a).2.componentSize = self.componentSize :=
  Impl.leaderFuel_componentSize n self a

theorem leader_fst {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (self.leader a).1 = self.persistentLeader a :=
  (Impl.leaderFuel_spec h n a (h.persistentLeaderFuel_eq a n (by omega))).1

theorem leader_Valid {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (self.leader a).2.Valid :=
  (Impl.leaderFuel_spec h n a (h.persistentLeaderFuel_eq a n (by omega))).2.1

@[simp] theorem leader_persistentLeader {self : UnionFind n} (h : self.Valid) (a c : Fin n) :
    (self.leader a).2.persistentLeader c = self.persistentLeader c :=
  (Impl.leaderFuel_spec h n a (h.persistentLeaderFuel_eq a n (by omega))).2.2 c

theorem same_fst {self : UnionFind n} (h : self.Valid) (a b : Fin n) :
    (self.same a b).1 = self.persistentSame a b := by
  show ((self.leader a).1 == ((self.leader a).2.leader b).1) = _
  rw [leader_fst h a, leader_fst (leader_Valid h a) b, leader_persistentLeader h a b]
  rfl

theorem same_Valid {self : UnionFind n} (h : self.Valid) (a b : Fin n) :
    (self.same a b).2.Valid :=
  leader_Valid (leader_Valid h a) b

@[simp] theorem same_persistentLeader {self : UnionFind n} (h : self.Valid) (a b c : Fin n) :
    (self.same a b).2.persistentLeader c = self.persistentLeader c := by
  show ((self.leader a).2.leader b).2.persistentLeader c = _
  rw [leader_persistentLeader (leader_Valid h a) b c, leader_persistentLeader h a c]

theorem size_fst {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (self.size a).1 = self.persistentSize a := by
  show (self.leader a).2.componentSize[(self.leader a).1] = _
  rw [leader_fst h a, leader_componentSize]
  rfl

/-- `size` answers that same count, and hands back the compressed state. -/
theorem size_fst_eq_card {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (self.size a).1 = (Finset.univ.filter fun v => self.persistentSame v a).card := by
  rw [size_fst h, persistentSize_eq_card h]

theorem size_Valid {self : UnionFind n} (h : self.Valid) (a : Fin n) :
    (self.size a).2.Valid :=
  leader_Valid h a

@[simp] theorem size_persistentLeader {self : UnionFind n} (h : self.Valid) (a c : Fin n) :
    (self.size a).2.persistentLeader c = self.persistentLeader c :=
  leader_persistentLeader h a c

theorem merge_eq (self : UnionFind n) (a b : Fin n) :
    self.merge a b =
      Impl.link ((self.leader a).2.leader b).2 (self.leader a).1
        ((self.leader a).2.leader b).1 := rfl

/-- The state `merge` walks through before linking has the same representatives
as the one it started from. -/
theorem merge_state_persistentLeader {self : UnionFind n} (h : self.Valid) (a b c : Fin n) :
    ((self.leader a).2.leader b).2.persistentLeader c = self.persistentLeader c := by
  rw [leader_persistentLeader (leader_Valid h a) b c, leader_persistentLeader h a c]

/-- `merge` keeps the invariant. -/
theorem merge_Valid {self : UnionFind n} (h : self.Valid) (a b : Fin n) :
    (self.merge a b).Valid := by
  have h2 := leader_Valid (leader_Valid h a) b
  have hs2 := merge_state_persistentLeader h a b
  rw [merge_eq]
  refine Impl.link_Valid h2 ?_ ?_
  · rw [leader_fst h a, ← hs2 a]
    exact h2.parent_persistentLeader a
  · rw [leader_fst (leader_Valid h a) b, leader_persistentLeader h a b, ← hs2 b]
    exact h2.parent_persistentLeader b

/-- `merge` joins the same two components `persistentMerge` does. -/
theorem merge_persistentSame {self : UnionFind n} (h : self.Valid) (a b c d : Fin n) :
    (self.merge a b).persistentSame c d ↔
      self.persistentSame c d ∨
        (self.persistentSame c a ∧ self.persistentSame d b) ∨
        (self.persistentSame c b ∧ self.persistentSame d a) := by
  have h2 := leader_Valid (leader_Valid h a) b
  have hs2 := merge_state_persistentLeader h a b
  have hxa : (self.leader a).1 = self.persistentLeader a := leader_fst h a
  have hyb : ((self.leader a).2.leader b).1 = self.persistentLeader b := by
    rw [leader_fst (leader_Valid h a) b, leader_persistentLeader h a b]
  simp only [persistentSame_iff, merge_eq]
  rw [Impl.link_persistentLeader_eq h2.toOrdered
    (by rw [hxa, ← hs2 a]; exact h2.parent_persistentLeader a)
    (by rw [hyb, ← hs2 b]; exact h2.parent_persistentLeader b) c d, hxa, hyb]
  simp only [hs2]

/-- The two families agree on connectivity: `merge` and `persistentMerge` differ
only in the paths they leave behind. -/
theorem merge_persistentSame_eq {self : UnionFind n} (h : self.Valid) (a b c d : Fin n) :
    (self.merge a b).persistentSame c d = (self.persistentMerge a b).persistentSame c d := by
  have h1 := merge_persistentSame h a b c d
  have h2 := persistentMerge_persistentSame h a b c d
  simp only [← h2] at h1
  exact Bool.eq_iff_iff.mpr h1


/-! ## `empty` -/

private theorem leaderFuel_empty {n : Nat} (fuel : Nat) (i : Fin n) :
    Impl.leaderFuel fuel (empty n) i = (i, empty n) := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih => simp [Impl.leaderFuel, empty]

@[simp] theorem empty_leader {n : Nat} (i : Fin n) :
    (empty n).leader i = (i, empty n) :=
  leaderFuel_empty n i

@[simp] theorem empty_size {n : Nat} (i : Fin n) :
    (empty n).size i = (1, empty n) := by
  simp only [size, empty_leader]
  simp [empty]

@[simp] theorem empty_same {n : Nat} (i j : Fin n) :
    (empty n).same i j = (i == j, empty n) := by
  simp [same]

@[simp] theorem empty_merge_self (a : Fin n) :
    (empty n).merge a a = empty n := by
  simp [merge, Impl.link]

@[simp] theorem empty_persistentMerge_self (a : Fin n) :
    (empty n).persistentMerge a a = empty n := by
  simp [persistentMerge, Impl.link]

/-! ## Tests -/

/-- Components come back in order of the first vertex belonging to each, and each
component lists its vertices in increasing order. -/
example :
    let uf := (empty 7).merge 1 3 |>.merge 5 1 |>.merge 4 6
    uf.groups.1 = #[#[0], #[1, 3, 5], #[2], #[4, 6]] := by
  native_decide

example : (empty 4).groups.1 = #[#[0], #[1], #[2], #[3]] := by
  native_decide

/-- The ordering still follows the least vertex of each component even when the
representative is not that vertex. -/
example :
    let uf := (empty 6).merge 5 0 |>.merge 4 1 |>.merge 3 2
    uf.groups.1 = #[#[0, 5], #[1, 4], #[2, 3]] := by
  native_decide

example :
    let uf := (empty 5).merge 0 1 |>.merge 3 4 |>.merge 1 4
    let (connected, uf) := uf.same 0 3
    let (separate, uf) := uf.same 0 2
    let (card, _) := uf.size 4
    connected && !separate && card == 4 := by
  native_decide

/-- The persistent family answers the same, without threading state. -/
example :
    let uf := (empty 5).persistentMerge 0 1 |>.persistentMerge 3 4 |>.persistentMerge 1 4
    uf.persistentSame 0 3 && !uf.persistentSame 0 2 && uf.persistentSize 4 == 4 := by
  native_decide

/-- The size a state records is the number of vertices connected, counted. -/
example :
    let uf := (empty 5).persistentMerge 0 1 |>.persistentMerge 3 4 |>.persistentMerge 1 4
    uf.persistentSize 4 = (Finset.univ.filter fun v => uf.persistentSame v 4).card := by
  decide

/-- In range, the `!` variants agree with the `Fin`-indexed originals. -/
example :
    let uf := (empty 5).merge! 0 1 |>.merge! 3 4 |>.merge! 1 4
    let (connected, uf) := uf.same! 0 3
    let (separate, uf) := uf.same! 0 2
    let (card, uf) := uf.size! 4
    let (root, _) := uf.leader! 4
    connected && !separate && card == 4 && root == 0 := by
  native_decide

example :
    let uf := (empty 5).persistentMerge! 0 1 |>.persistentMerge! 3 4 |>.persistentMerge! 1 4
    uf.persistentSame! 0 3 && !uf.persistentSame! 0 2 &&
      uf.persistentSize! 4 == 4 && uf.persistentLeader! 4 == 0 := by
  native_decide

example :
    let uf := empty 5
    (uf.leader? 4).isSome && (uf.leader? 5).isNone &&
      (uf.merge? 4 0).isSome && (uf.merge? 5 0).isNone &&
      (uf.same? 0 4).isSome && (uf.same? 0 5).isNone &&
      (uf.size? 4).isSome && (uf.size? 5).isNone := by
  native_decide

example :
    let uf := empty 5
    (uf.persistentLeader? 4).isSome && (uf.persistentLeader? 5).isNone &&
      (uf.persistentMerge? 4 0).isSome && (uf.persistentMerge? 5 0).isNone &&
      (uf.persistentSame? 0 4).isSome && (uf.persistentSame? 0 5).isNone &&
      (uf.persistentSize? 4).isSome && (uf.persistentSize? 5).isNone := by
  native_decide

end UnionFind

end Cplib
