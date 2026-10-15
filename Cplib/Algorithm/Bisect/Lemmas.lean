import Cplib.Algorithm.Bisect.Basic

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
