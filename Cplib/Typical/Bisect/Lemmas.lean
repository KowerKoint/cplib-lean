import Cplib.Typical.Bisect.Basic
import Mathlib.Tactic

theorem bisectMax'_bounds (hokng : ok < ng) (p : Nat → Bool) :
    ok ≤ bisectMax' ok ng p ∧ bisectMax' ok ng p < ng := by
  refine (bisectMax'.induct p (motive := fun l r =>
    l < r → l ≤ bisectMax' l r p ∧ bisectMax' l r p < r)
    ?_ ?_ ?_ ok ng) hokng
  · intro l r h mid hmid ih _
    subst mid
    let mid := Nat.midpoint l r h
    rw [bisectMax'.eq_1]
    simp only [dif_pos h, hmid]
    have hbounds := ih mid.hvr
    exact ⟨Nat.le_trans (Nat.le_of_lt mid.hlv) hbounds.1, hbounds.2⟩
  · intro l r h mid hmid ih _
    subst mid
    let mid := Nat.midpoint l r h
    rw [bisectMax'.eq_1]
    simp only [dif_pos h, hmid]
    have hbounds := ih mid.hlv
    exact ⟨hbounds.1, Nat.lt_trans hbounds.2 mid.hvr⟩
  · intro l r h hlr
    rw [bisectMax'.eq_1]
    simp [h, hlr]

theorem bisectMin'_bounds (hngok : ng < ok) (p : Nat → Bool) :
    ng < bisectMin' ng ok p ∧ bisectMin' ng ok p ≤ ok := by
  simp only [bisectMin']
  have h := bisectMax'_bounds hngok (fun x => !(p x))
  omega

theorem bisectMaxBelow_le (ng : Nat) (p : Fin ng → Bool) :
    bisectMaxBelow ng p ≤ ng := by
  unfold bisectMaxBelow
  have h := bisectMax'_bounds (Nat.zero_lt_succ ng) (fun x =>
    if x = 0 then true
    else if hx : x.pred < ng then p ⟨x.pred, hx⟩ else false)
  exact Nat.le_trans (Nat.pred_le _) (Nat.le_of_lt_succ h.2)

theorem bisectMinBelow_le (ok : Nat) (p : Fin ok → Bool) :
    bisectMinBelow ok p ≤ ok := by
  unfold bisectMinBelow
  have h := bisectMin'_bounds (Nat.zero_lt_succ ok) (fun x =>
    if x = 0 then false
    else if hx : x.pred < ok then p ⟨x.pred, hx⟩ else true)
  exact Nat.pred_le_iff_le_succ.mpr h.2

def monotoneTrueToFalse (p : Nat → Bool) :=
  ∀ x y, x ≤ y → p y → p x

theorem bisectMax_spec (hokng : ok < ng) (p : Nat → Bool)
    (hmono : monotoneTrueToFalse p) :
    let res := bisectMax' ok ng p
    (ok ≤ res ∧ res < ng) ∧
    ∀ x, ok < x → x < ng → if x ≤ res then p x else ¬p x := by
  refine (bisectMax'.induct p (motive := fun l r =>
    l < r →
    let res := bisectMax' l r p
    (l ≤ res ∧ res < r) ∧
    ∀ x, l < x → x < r → if x ≤ res then p x else ¬p x
  ) ?_ ?_ ?_ ok ng) hokng
  · intro l r h mid hmid ih _
    subst mid
    let mid := Nat.midpoint l r h
    have hrec : bisectMax' l r p = bisectMax' mid.v r p := by
      rw [bisectMax'.eq_1]
      simp [mid, h, hmid]
    obtain ⟨⟨hmidres, hresr⟩, hspec⟩ :
        (mid.v ≤ bisectMax' mid.v r p ∧ bisectMax' mid.v r p < r) ∧
        ∀ x, mid.v < x → x < r →
          if x ≤ bisectMax' mid.v r p then p x else ¬p x := by
      simpa [mid] using ih mid.hvr
    rw [hrec]
    refine ⟨⟨Nat.le_trans (Nat.le_of_lt mid.hlv) hmidres, hresr⟩, ?_⟩
    intro x hlx hxr
    by_cases hxm : x ≤ mid.v
    · have hpx : p x := hmono x mid.v hxm (by simpa [mid] using hmid)
      simp [if_pos (Nat.le_trans hxm hmidres), hpx]
    · exact hspec x (by omega) hxr
  · intro l r h mid hmid ih _
    subst mid
    let mid := Nat.midpoint l r h
    have hrec : bisectMax' l r p = bisectMax' l mid.v p := by
      rw [bisectMax'.eq_1]
      simp [mid, h, hmid]
    obtain ⟨⟨hlres, hresmid⟩, hspec⟩ :
        (l ≤ bisectMax' l mid.v p ∧ bisectMax' l mid.v p < mid.v) ∧
        ∀ x, l < x → x < mid.v →
          if x ≤ bisectMax' l mid.v p then p x else ¬p x := by
      simpa [mid] using ih mid.hlv
    rw [hrec]
    refine ⟨⟨hlres, Nat.lt_trans hresmid mid.hvr⟩, ?_⟩
    intro x hlx hxr
    by_cases hxm : x < mid.v
    · exact hspec x hlx hxm
    · have hmidFalse : ¬p mid.v := by simpa [mid] using hmid
      have hpx : ¬p x := fun hpx => hmidFalse (hmono mid.v x (by omega) hpx)
      have hresx : bisectMax' l mid.v p < x :=
        Nat.lt_of_lt_of_le hresmid (by omega)
      simp [Nat.not_le_of_lt hresx, hpx]
  · intro l r h hlr
    rw [bisectMax'.eq_1]
    simp only [dif_neg h]
    refine ⟨⟨Nat.le_refl l, hlr⟩, ?_⟩
    intro x hlx hxr
    omega

def monotoneFalseToTrue (p : Nat → Bool) :=
  ∀ x y, x ≤ y → p x → p y

theorem bisectMin_spec (hngok : ng < ok) (p : Nat → Bool)
    (hmono : monotoneFalseToTrue p) :
    let res := bisectMin' ng ok p
    (ng < res ∧ res ≤ ok) ∧
    ∀ x, ng < x → x < ok → if res ≤ x then p x else ¬p x := by
  have hmonoNot : monotoneTrueToFalse (fun x => !(p x)) := by
    intro x y hxy hy
    by_cases hx : p x
    · have hpy := hmono x y hxy hx
      simp_all
    · simp_all
  obtain ⟨⟨hngres, hresok⟩, hspec⟩ :=
    bisectMax_spec hngok (fun x => !(p x)) hmonoNot
  simp only [bisectMin']
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro x hngx hxok
  have hxspec := hspec x hngx hxok
  by_cases hresx : (bisectMax' ng ok fun x => !(p x)).succ ≤ x
  · have hxgt : ¬x ≤ bisectMax' ng ok (fun x => !(p x)) := by omega
    simp [hresx, hxgt] at hxspec ⊢
    exact hxspec
  · have hxle : x ≤ bisectMax' ng ok (fun x => !(p x)) := by omega
    simp [hresx, hxle] at hxspec ⊢
    exact hxspec

def monotoneFalseToTrueFin (p : Fin n → Bool) :=
  ∀ i j, i ≤ j → p i → p j

theorem bisectMinBelow_spec (p : Fin ok → Bool)
    (hmono : monotoneFalseToTrueFin p) :
    let res := bisectMinBelow ok p
    res ≤ ok ∧ ∀ i : Fin ok, if res ≤ i.val then p i else ¬p i := by
  let p' (x : Nat) : Bool :=
    if x = 0 then false
    else if hx : x.pred < ok then p ⟨x.pred, hx⟩ else true
  have hpmono : monotoneFalseToTrue p' := by
    intro x y hxy hx
    by_cases hx0 : x = 0
    · simp [p', hx0] at hx
    have hpred : x.pred ≤ y.pred := Nat.pred_le_pred hxy
    by_cases hxok : x.pred < ok
    · have hpx : p ⟨x.pred, hxok⟩ := by
        dsimp only [p'] at hx
        rw [if_neg hx0, dif_pos hxok] at hx
        exact hx
      have hy0 : y ≠ 0 := by omega
      by_cases hyok : y.pred < ok
      · have hxy' : (⟨x.pred, hxok⟩ : Fin ok) ≤ ⟨y.pred, hyok⟩ := by
          simp only [Fin.mk_le_mk]
          exact hpred
        dsimp only [p']
        rw [if_neg hy0, dif_pos hyok]
        exact hmono _ _ hxy' hpx
      · dsimp only [p']
        rw [if_neg hy0, dif_neg hyok]
    · have hy0 : y ≠ 0 := by omega
      have hyok : ¬y.pred < ok := fun hyok => hxok (lt_of_le_of_lt hpred hyok)
      dsimp only [p']
      rw [if_neg hy0, dif_neg hyok]
  have hspec := bisectMin_spec (Nat.zero_lt_succ ok) p' hpmono
  let raw := bisectMin' 0 ok.succ p'
  have hraw : 0 < raw ∧ raw ≤ ok.succ := by
    simpa [raw] using hspec.1
  have hres : bisectMinBelow ok p = raw.pred := by
    rfl
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact Nat.pred_le_iff_le_succ.mpr hraw.2
  · intro i
    rw [hres]
    have hi := i.isLt
    have hiSpec := hspec.2 (i.val + 1) (by omega) (by omega)
    have hrawEq : bisectMin' 0 ok.succ p' = raw := rfl
    rw [hrawEq] at hiSpec
    have hpredEq : raw.pred + 1 = raw := Nat.succ_pred_eq_of_pos hraw.1
    by_cases hrawle : raw ≤ i.val + 1
    · have hle : raw.pred ≤ i.val := by omega
      rw [if_pos hle]
      rw [if_pos hrawle] at hiSpec
      simpa [p'] using hiSpec
    · have hle : ¬raw.pred ≤ i.val := by omega
      rw [if_neg hle]
      rw [if_neg hrawle] at hiSpec
      simpa [p'] using hiSpec

namespace Array

theorem lowerBound_le_size [Ord α] (xs : Array α) (a : α) :
    xs.lowerBound a ≤ xs.size :=
  bisectMinBelow_le xs.size _

theorem upperBound_le_size [Ord α] (xs : Array α) (a : α) :
    xs.upperBound a ≤ xs.size :=
  bisectMinBelow_le xs.size _

theorem lowerBound_spec [LinearOrder α] (xs : Array α)
    (hsorted : xs.toList.Sorted (· ≤ ·)) (a : α) :
    xs.lowerBound a ≤ xs.size ∧
      (∀ i : Fin xs.size, i.val < xs.lowerBound a → xs[i] < a) ∧
      (∀ i : Fin xs.size, xs.lowerBound a ≤ i.val → a ≤ xs[i]) := by
  let p : Fin xs.size → Bool := fun i => compare xs[i] a != Ordering.lt
  have hpmono : monotoneFalseToTrueFin p := by
    intro i j hij hi
    have hxle : xs[i] ≤ xs[j] := by
      simpa using hsorted.rel_get_of_le hij
    have hai : a ≤ xs[i] := by
      have hncmp : ¬compare xs[i] a = Ordering.lt := by simpa [p] using hi
      exact not_lt.mp (fun hlt => hncmp (compare_lt_iff_lt.mpr hlt))
    have haj : a ≤ xs[j] := le_trans hai hxle
    have hncmp : ¬compare xs[j] a = Ordering.lt :=
      fun hc => (not_lt.mpr haj) (compare_lt_iff_lt.mp hc)
    simpa [p] using hncmp
  have hspec := bisectMinBelow_spec p hpmono
  have hlb : xs.lowerBound a = bisectMinBelow xs.size p := rfl
  rw [hlb]
  refine ⟨hspec.1, ?_, ?_⟩
  · intro i hi
    have h := hspec.2 i
    simp only [if_neg (by omega : ¬bisectMinBelow xs.size p ≤ i.val)] at h
    exact compare_lt_iff_lt.mp (by simpa [p] using h)
  · intro i hi
    have h := hspec.2 i
    simp only [if_pos hi] at h
    have hncmp : ¬compare xs[i] a = Ordering.lt := by simpa [p] using h
    exact not_lt.mp (fun hlt => hncmp (compare_lt_iff_lt.mpr hlt))

theorem upperBound_spec [LinearOrder α] (xs : Array α)
    (hsorted : xs.toList.Sorted (· ≤ ·)) (a : α) :
    xs.upperBound a ≤ xs.size ∧
      (∀ i : Fin xs.size, i.val < xs.upperBound a → xs[i] ≤ a) ∧
      (∀ i : Fin xs.size, xs.upperBound a ≤ i.val → a < xs[i]) := by
  let p : Fin xs.size → Bool := fun i => compare xs[i] a == Ordering.gt
  have hpmono : monotoneFalseToTrueFin p := by
    intro i j hij hi
    have hxle : xs[i] ≤ xs[j] := by
      simpa using hsorted.rel_get_of_le hij
    have hai : a < xs[i] := compare_gt_iff_gt.mp (by simpa [p] using hi)
    have haj : a < xs[j] := lt_of_lt_of_le hai hxle
    simpa [p] using compare_gt_iff_gt.mpr haj
  have hspec := bisectMinBelow_spec p hpmono
  have hub : xs.upperBound a = bisectMinBelow xs.size p := rfl
  rw [hub]
  refine ⟨hspec.1, ?_, ?_⟩
  · intro i hi
    have h := hspec.2 i
    simp only [if_neg (by omega : ¬bisectMinBelow xs.size p ≤ i.val)] at h
    apply not_lt.mp
    intro hai
    apply h
    simpa [p] using compare_gt_iff_gt.mpr hai
  · intro i hi
    have h := hspec.2 i
    simp only [if_pos hi] at h
    exact compare_gt_iff_gt.mp (by simpa [p] using h)

end Array
