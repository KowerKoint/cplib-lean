import Cplib.NumberTheory.Prime.Basic
import Cplib.NumberTheory.Modular.Lemmas
import Cplib.Util.List.Lemmas
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace Cplib

/-!
# NumberTheory.Prime.Lemmas

What can be proved about the primality test and the factorisation in
`NumberTheory.Prime.Basic`, and what cannot.

`isPrime_of_prime` is the half that is a theorem: a prime passes every base.
The sequence `a ^ d, a ^ 2d, a ^ 4d, …` ends at `1` by Fermat's little theorem,
and the only square roots of `1` in a field are `1` and `-1`, so the first `1`
along it is reached either from the start or from `-1`, which is what the test
looks for.

The other half, that a number passing every base is prime, is **not** proved
and cannot be from inside Lean: it is the outcome of the exhaustive searches
cited in `Prime.Basic`, which hold below `3317044064679887385961981` and are
open beyond it. Nothing in this file assumes it.

The factorisation is specified by what does not depend on that: the factors
multiply back to the number (`primeFactors_prod`, `factorize_prod`), they come
out in increasing order (`primeFactors_sorted`), and everything `divisors`
lists divides (`mem_divisors_dvd`). That the factors are *prime*, and that
`divisors` lists them *all*, rests on `isPrime` and is left to the citations.
-/

namespace NumberTheory
namespace Impl

theorem oddPart_spec (m : Nat) :
    (oddPart m).1 * 2 ^ (oddPart m).2 = m ∧ (0 < m → (oddPart m).1 % 2 = 1) := by
  fun_induction oddPart m with
  | case1 m h => simpa using fun _ => h.resolve_left (by omega)
  | case2 m h d s ih1 ih =>
      rw [ih1] at ih
      obtain ⟨hprod, hodd⟩ := ih
      simp only at hprod hodd ⊢
      refine ⟨?_, fun _ => hodd (by omega)⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, hprod]
      omega

/-- A witness `j` that squaring reaches `n - 1` makes the loop say so. -/
theorem sprpLoop_eq_true {n : Nat} :
    ∀ s j y : Nat, j < s → y ^ 2 ^ j % n = n - 1 → sprpLoop n s (y % n) = true := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro j y hj h
      rw [sprpLoop]
      match j with
      | 0 =>
          simp only [Nat.pow_zero, Nat.pow_one] at h
          simp [h]
      | j + 1 =>
          have hstep : y % n * (y % n) % n = y ^ 2 % n := by
            rw [← Nat.mul_mod, Nat.pow_two]
          have hpow : (y ^ 2) ^ 2 ^ j = y ^ 2 ^ (j + 1) := by
            rw [← Nat.pow_mul, Nat.pow_succ]
            ring_nf
          rw [hstep, ← Nat.mod_mod_of_dvd _ (dvd_refl n)]
          simp only [Bool.or_eq_true]
          exact Or.inr (ih j (y ^ 2) (by omega) (by rw [hpow]; exact h))

/-- A prime passes the test to every base it does not divide.

This is the half of Miller-Rabin that is a theorem rather than a search: the
sequence `a ^ d, a ^ (2d), a ^ (4d), …` ends at `1` by Fermat, and in a field
the only square roots of `1` are `1` and `-1`, so the first `1` in that
sequence is reached either from the start or from `-1`. -/
theorem isSprp_of_prime {n : Nat} (hn : n.Prime) (h2 : 2 < n) {a : Nat} (ha : ¬n ∣ a) :
    isSprp n a = true := by
  haveI : Fact n.Prime := ⟨hn⟩
  classical
  obtain ⟨hprod, -⟩ := oddPart_spec (n - 1)
  set d := (oddPart (n - 1)).1 with hd
  set s := (oddPart (n - 1)).2 with hs
  have hα : (a : ZMod n) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a n).mp h)
  have hex : ∃ r, (a : ZMod n) ^ (d * 2 ^ r) = 1 :=
    ⟨s, by rw [hprod]; exact ZMod.pow_card_sub_one_eq_one hα⟩
  have hrs : Nat.find hex ≤ s := Nat.find_le (by rw [hprod]; exact ZMod.pow_card_sub_one_eq_one hα)
  have hcast : ∀ e : Nat, ((a ^ e : Nat) : ZMod n) = (a : ZMod n) ^ e := fun e => by push_cast; ring
  have hy : powMod a d n = a ^ d % n := powMod_eq a d (by omega)
  rw [isSprp]
  simp only [← hd, ← hs, hy, Bool.or_eq_true, beq_iff_eq]
  rcases hfind : Nat.find hex with r | r
  · -- the walk starts at 1
    left
    have h1 : ((a ^ d : Nat) : ZMod n) = ((1 : Nat) : ZMod n) := by
      rw [hcast, Nat.cast_one]
      have := Nat.find_spec hex
      rw [hfind] at this
      simpa using this
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rw [this, Nat.one_mod_eq_one.mpr (by omega)]
  · -- the walk reaches 1 from -1
    right
    have hne : (a : ZMod n) ^ (d * 2 ^ r) ≠ 1 := Nat.find_min hex (by omega)
    have hsq : (a : ZMod n) ^ (d * 2 ^ r) * (a : ZMod n) ^ (d * 2 ^ r) = 1 := by
      rw [← pow_add]
      have hrr : d * 2 ^ r + d * 2 ^ r = d * 2 ^ (r + 1) := by ring
      rw [hrr, ← hfind]
      exact Nat.find_spec hex
    have hneg : (a : ZMod n) ^ (d * 2 ^ r) = -1 := (mul_self_eq_one_iff.mp hsq).resolve_left hne
    have hcastneg : ((n - 1 : Nat) : ZMod n) = -1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
    have hmod : a ^ (d * 2 ^ r) % n = (n - 1) % n := by
      refine (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_
      rw [hcast, hcastneg]
      exact hneg
    refine sprpLoop_eq_true s r (a ^ d) (by omega) ?_
    rw [← Nat.pow_mul, hmod, Nat.mod_eq_of_lt (by omega)]

end Impl

/-- Every prime passes `isPrime`.

The converse is not proved here, and cannot be: it is the outcome of the
exhaustive searches cited in `Prime.Basic`, which hold below
`3317044064679887385961981` and are open beyond it. -/
theorem isPrime_of_prime {n : Nat} (hn : n.Prime) : isPrime n = true := by
  rw [isPrime, if_neg (by have := hn.two_le; omega)]
  by_cases hsmall : Impl.smallPrimes.any (fun p => n == p) = true
  · rw [if_pos hsmall]
  · rw [if_neg hsmall]
    have hne : ∀ p ∈ Impl.smallPrimes, n ≠ p := by
      intro p hp hnp
      exact hsmall (List.any_eq_true.mpr ⟨p, hp, by simp [hnp]⟩)
    have hnotdvd : ¬Impl.smallPrimes.any (fun p => n % p == 0) = true := by
      intro hc
      obtain ⟨p, hp, hmod⟩ := List.any_eq_true.mp hc
      have hpp : p.Prime := by fin_cases hp <;> norm_num
      have hpn : p ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using hmod)
      exact hne p hp ((Nat.prime_dvd_prime_iff_eq hpp hn).mp hpn).symm
    rw [if_neg hnotdvd]
    have h61 : 61 < n := by
      by_contra hc
      push_neg at hc
      have hmem : n ∈ Impl.smallPrimes := by
        have h2 := hn.two_le
        interval_cases n <;> revert hn <;> decide
      exact hne n hmem rfl
    simp only [List.all_eq_true]
    intro a ha
    have hbound : 0 < a ∧ a < n := by
      split at ha
      · have : a = 2 ∨ a = 7 ∨ a = 61 := by simpa [Impl.smallBases] using ha
        omega
      · split at ha
        · have : a = 2 ∨ a = 325 ∨ a = 9375 ∨ a = 28178 ∨ a = 450775 ∨ a = 9780504 ∨
              a = 1795265022 := by simpa [Impl.wideBases] using ha
          omega
        · have : a = 2 ∨ a = 3 ∨ a = 5 ∨ a = 7 ∨ a = 11 ∨ a = 13 ∨ a = 17 ∨ a = 19 ∨ a = 23 ∨
              a = 29 ∨ a = 31 ∨ a = 37 := by simpa [Impl.hugeBases] using ha
          omega
    exact Impl.isSprp_of_prime hn (by omega) fun hdvd => by
      have := Nat.le_of_dvd hbound.1 hdvd
      omega

namespace Impl

/-- Whatever rho hands back is a factor of `n`, and neither `1` nor `n`. -/
theorem rhoLoop_dvd {n c : Nat} : ∀ fuel x y d : Nat,
    rhoLoop n c fuel x y = some d → d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
  intro fuel
  induction fuel with
  | zero => intro x y d h; simp [rhoLoop] at h
  | succ fuel ih =>
      intro x y d h
      rw [rhoLoop] at h
      split at h
      · exact ih _ _ _ h
      · split at h
        · simp at h
        · simp only [Option.some.injEq] at h
          subst h
          rename_i h1 h2
          exact ⟨Nat.gcd_dvd_right _ _, by simpa using h1, by simpa using h2⟩

theorem findFactor_dvd {n steps : Nat} : ∀ attempts c d : Nat,
    findFactor n steps attempts c = some d → d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
  intro attempts
  induction attempts with
  | zero => intro c d h; simp [findFactor] at h
  | succ attempts ih =>
      intro c d h
      rw [findFactor] at h
      split at h
      · rename_i e he
        simp only [Option.some.injEq] at h
        subst h
        exact rhoLoop_dvd _ _ _ _ he
      · exact ih _ _ h

/-- The factors multiply back to the number they came from, whether or not the
splitting ran to completion. -/
theorem factorsAux_prod : ∀ (fuel n : Nat), 0 < n → (factorsAux n fuel).prod = n := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn
      rw [factorsAux]
      split
      · simp; omega
      · simp
  | succ fuel ih =>
      intro n hn
      rw [factorsAux]
      split
      · simp; omega
      · split
        · simp
        · split
          · rename_i p hp
            have hdvd : p ∣ n := by
              have := List.find?_some hp
              exact Nat.dvd_of_mod_eq_zero (by simpa using this)
            have hppos : 0 < p := by
              have := List.mem_of_find?_eq_some hp
              fin_cases this <;> omega
            rw [List.prod_cons, ih (n / p) (Nat.div_pos (Nat.le_of_dvd hn hdvd) hppos),
              Nat.mul_div_cancel' hdvd]
          · split
            · rename_i d hd
              obtain ⟨hdvd, hd1, hdn⟩ := findFactor_dvd _ _ _ hd
              have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
              rw [List.prod_append, ih d hdpos,
                ih (n / d) (Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos),
                Nat.mul_div_cancel' hdvd]
            · simp

end Impl

/-- The factors multiply back to `n`. -/
theorem primeFactors_prod {n : Nat} (hn : 0 < n) : (primeFactors n).toList.prod = n := by
  rw [primeFactors]
  rw [(List.mergeSort_perm _ _).prod_eq]
  exact Impl.factorsAux_prod _ n hn

/-- …and so do the prime powers. -/
theorem factorize_prod {n : Nat} (hn : 0 < n) :
    ((factorize n).toList.map fun pe => pe.1 ^ pe.2).prod = n := by
  rw [factorize]
  rw [List.runLength_prod, (List.mergeSort_perm _ _).prod_eq]
  exact Impl.factorsAux_prod _ n hn

/-- The factors come out in increasing order. -/
theorem primeFactors_sorted (n : Nat) : (primeFactors n).toList.Sorted (· ≤ ·) := by
  rw [primeFactors]
  exact List.sorted_mergeSort' _ _

namespace Impl

theorem divisorStep_dvd {m : Nat} {acc : List Nat} (hacc : ∀ a ∈ acc, a ∣ m) (pe : Nat × Nat) :
    ∀ d ∈ divisorStep acc pe, d ∣ m * pe.1 ^ pe.2 := by
  intro d hd
  simp only [divisorStep, List.mem_flatMap, List.mem_map, List.mem_range] at hd
  obtain ⟨i, hi, a, ha, rfl⟩ := hd
  exact Nat.mul_dvd_mul (hacc a ha) (Nat.pow_dvd_pow _ (by omega))

theorem foldl_divisorStep_dvd : ∀ (l : List (Nat × Nat)) (acc : List Nat) (m : Nat),
    (∀ a ∈ acc, a ∣ m) → ∀ d ∈ l.foldl divisorStep acc,
      d ∣ m * (l.map fun pe => pe.1 ^ pe.2).prod := by
  intro l
  induction l with
  | nil =>
      intro acc m hacc d hd
      simpa using hacc d hd
  | cons pe l ih =>
      intro acc m hacc d hd
      rw [List.foldl_cons] at hd
      have hstep := ih (divisorStep acc pe) (m * pe.1 ^ pe.2) (divisorStep_dvd hacc pe) d hd
      simpa [List.map_cons, List.prod_cons, Nat.mul_assoc] using hstep

end Impl

/-- Everything `divisors` lists really does divide. That it lists *every*
divisor rests on the factorisation being complete, which rests in turn on
`isPrime`; see the module docstring of `Prime.Basic`. -/
theorem mem_divisors_dvd {n d : Nat} (hn : 0 < n) (h : d ∈ divisors n) : d ∣ n := by
  rw [divisors, if_neg (by omega)] at h
  rw [Array.mem_toArray, (List.mergeSort_perm _ _).mem_iff] at h
  have := Impl.foldl_divisorStep_dvd (factorize n).toList [1] 1 (by simp) d h
  rwa [Nat.one_mul, factorize_prod hn] at this

/-! ## Tests -/

example : isPrime 998244353 := by native_decide
example : isPrime 1000000007 := by native_decide
example : isPrime (2 ^ 61 - 1) := by native_decide
example : isPrime (2 ^ 64 - 59) := by native_decide
example : !isPrime 3215031751 := by native_decide
example : (List.range 100).filter isPrime =
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
      97] := by native_decide

example : factorize 1000000016000000063 = #[(1000000007, 1), (1000000009, 1)] := by native_decide
example : factorize 1000000056000000343 = #[(23, 1), (853, 1), (50971, 1), (1000000007, 1)] := by
  native_decide
example : primeFactors 360 = #[2, 2, 2, 3, 3, 5] := by native_decide
example : factorize 360 = #[(2, 3), (3, 2), (5, 1)] := by native_decide
example : divisors 36 = #[1, 2, 3, 4, 6, 9, 12, 18, 36] := by native_decide
example : primeFactors 1 = #[] := by native_decide
example : divisors 1 = #[1] := by native_decide

end NumberTheory

end Cplib
