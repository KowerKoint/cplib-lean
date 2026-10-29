import Cplib.NumberTheory.Sieve.Basic
import Cplib.Util.List.Lemmas
import Mathlib.Tactic

namespace Cplib

/-!
# NumberTheory.Sieve.Lemmas

Specification of the sieve in `NumberTheory.Sieve.Basic`.

The table and the list of primes are pinned exactly: `build_minFactor` says
every entry from `2` on holds `Nat.minFac`, and `build_primes` says the list is
the primes up to `n` in increasing order. Everything else is read off those,
including that `isPrime` agrees with `Nat.Prime`.

Unlike the Miller-Rabin test in `NumberTheory.Prime`, nothing here is left to a
citation: the factorisation a sieve produces is proved complete, its factors
proved prime, and their order proved increasing.

The proof carries two invariants along the loop: the table holds the least
prime factor of every number whose least prime factor is below the index
reached, and nothing elsewhere; and the list holds the primes below that index.
What makes the first survive a round is that `i` marks only from `i * i`: a
multiple `i * m` with `m < i` has a smaller prime factor, so it was filled in
an earlier round, and the marking skips what is already filled.
-/

namespace NumberTheory
namespace Sieve
namespace Impl

/-- Marking writes `i` exactly where the progression from `j` lands on a slot
that nothing has claimed. -/
theorem markFrom_getElem (n i : Nat) (hi : 0 < i) :
    ∀ (spf : Vector Nat (n + 1)) (j t : Nat) (ht : t < n + 1),
      (markFrom n i hi spf j)[t] =
        if j ≤ t ∧ i ∣ t - j ∧ spf[t] = 0 then i else spf[t] := by
  intro spf j
  fun_induction markFrom n i hi spf j with
  | case1 spf j h spf' ih =>
      intro t ht
      have hspf' : ∀ u (hu : u < n + 1), spf'[u] =
          if u = j then (if spf[j]'(by omega) = 0 then i else spf[j]'(by omega)) else spf[u] := by
        intro u hu
        show (if spf[j]'(by omega) == 0 then spf.set j i (by omega) else spf)[u] = _
        by_cases huj : u = j
        · subst huj
          split
          · rename_i hz
            simp only [beq_iff_eq] at hz
            rw [Vector.getElem_set, if_pos rfl, if_pos rfl, if_pos hz]
          · rename_i hz
            simp only [beq_iff_eq] at hz
            rw [if_pos rfl, if_neg hz]
        · rw [if_neg huj]
          split
          · rw [Vector.getElem_set, if_neg fun hju => huj hju.symm]
          · rfl
      rw [ih t ht, hspf' t ht]
      by_cases htj : t = j
      · subst htj
        have hfalse : ¬t + i ≤ t := by omega
        simp [hfalse]
      · rw [if_neg htj]
        have hiff : (j + i ≤ t ∧ i ∣ t - (j + i)) ↔ (j ≤ t ∧ i ∣ t - j) := by
          constructor
          · rintro ⟨hle, hdvd⟩
            refine ⟨by omega, ?_⟩
            have hrw : t - j = t - (j + i) + i := by omega
            rw [hrw]
            exact Nat.dvd_add hdvd (Nat.dvd_refl i)
          · rintro ⟨hle, hdvd⟩
            have hge : i ≤ t - j := Nat.le_of_dvd (by omega) hdvd
            refine ⟨by omega, ?_⟩
            have hrw : t - (j + i) = t - j - i := by omega
            rw [hrw]
            exact Nat.dvd_sub hdvd (Nat.dvd_refl i)
        by_cases hz : spf[t]'ht = 0
        · by_cases hmem : j ≤ t ∧ i ∣ t - j
          · rw [if_pos ⟨(hiff.mpr hmem).1, (hiff.mpr hmem).2, hz⟩, if_pos ⟨hmem.1, hmem.2, hz⟩]
          · rw [if_neg fun hc => hmem (hiff.mp ⟨hc.1, hc.2.1⟩), if_neg fun hc => hmem ⟨hc.1, hc.2.1⟩]
        · rw [if_neg fun hc => hz hc.2.2, if_neg fun hc => hz hc.2.2]
  | case2 spf j h =>
      intro t ht
      rw [if_neg (by omega)]

/-- A number whose least prime factor is `p`, and that is not `p` itself, is at
least `p * p`: what is left after dividing `p` out has no factor below `p`. -/
theorem sq_le_of_minFac_eq {t p : Nat} (ht : 2 ≤ t) (hp : t.minFac = p) (hne : t ≠ p) :
    p * p ≤ t := by
  obtain ⟨m, hm⟩ : p ∣ t := hp ▸ Nat.minFac_dvd t
  have hpprime : p.Prime := hp ▸ Nat.minFac_prime (by omega)
  have hm1 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> omega
    · exact h
  have hmdvd : m.minFac ∣ t := hm ▸ Dvd.dvd.mul_left (Nat.minFac_dvd m) p
  have hle : p ≤ m.minFac :=
    hp ▸ Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le hmdvd
  calc p * p ≤ p * m := Nat.mul_le_mul_left p (Nat.le_trans hle (Nat.minFac_le (by omega)))
    _ = t := hm.symm

/-- What the table holds once every number below `i` has been sieved: the least
prime factor of each number that has one below `i`, and nothing elsewhere. -/
def Filled (n i : Nat) (spf : Vector Nat (n + 1)) : Prop :=
  ∀ t (ht : t < n + 1), spf[t] = if 2 ≤ t ∧ t.minFac < i then t.minFac else 0

/-- …and the primes recorded so far are exactly those below `i`. -/
def Listed (i : Nat) (primes : Array Nat) : Prop :=
  primes.toList = (List.range i).filter fun p => decide p.Prime

/-- The sieve fills the table with least prime factors and lists the primes. -/
theorem sieveFrom_spec (n : Nat) :
    ∀ (spf : Vector Nat (n + 1)) (primes : Array Nat) (i : Nat), 2 ≤ i →
      Filled n i spf → Listed i primes →
      Filled n (max i (n + 1)) (sieveFrom n spf primes i).1 ∧
        Listed (max i (n + 1)) (sieveFrom n spf primes i).2 := by
  intro spf primes i
  fun_induction sieveFrom n spf primes i with
  | case1 spf primes i hle hcond spf₁ spf₂ =>
      rename_i ih
      intro h2 hfill hlist
      rw [Nat.max_eq_right (by omega)]
      have hz : spf[i]'(by omega) = 0 := by simpa using hcond.2
      have hprime : i.Prime := by
        rw [Nat.prime_def_minFac]
        refine ⟨h2, ?_⟩
        by_contra hne
        have hlt : i.minFac < i := Nat.lt_of_le_of_ne (Nat.minFac_le (by omega)) hne
        have hval := hfill i (by omega)
        rw [if_pos ⟨h2, hlt⟩] at hval
        rw [hval] at hz
        exact absurd hz (by have := (Nat.minFac_prime (show i ≠ 1 by omega)).two_le; omega)
      have hset : ∀ u (hu : u < n + 1), (spf.set i i (by omega))[u] =
          if u = i then i else spf[u] := by
        intro u hu
        rw [Vector.getElem_set]
        by_cases hui : u = i
        · simp [hui]
        · rw [if_neg fun hiu => hui hiu.symm, if_neg hui]
      rw [Nat.max_eq_right (show i + 1 ≤ n + 1 by omega)] at ih
      refine ih (by omega) ?_ ?_
      · intro t ht
        show (markFrom n i (by omega) (spf.set i i (by omega)) (i * i))[t] = _
        rw [markFrom_getElem n i (by omega) _ _ t ht, hset t ht]
        by_cases hti : t = i
        · subst hti
          have hsq : ¬t * t ≤ t := by nlinarith [h2]
          rw [if_neg (by tauto), if_pos rfl,
            if_pos ⟨h2, by rw [(Nat.prime_def_minFac.mp hprime).2]; omega⟩,
            (Nat.prime_def_minFac.mp hprime).2]
        · rw [if_neg hti]
          by_cases hfac : 2 ≤ t ∧ t.minFac < i
          · have hval := hfill t ht
            rw [if_pos hfac] at hval
            have hne0 : spf[t] ≠ 0 := by
              rw [hval]
              have := (Nat.minFac_prime (show t ≠ 1 by omega)).two_le
              omega
            rw [if_neg (by tauto), hval, if_pos ⟨hfac.1, by omega⟩]
          · have hval := hfill t ht
            rw [if_neg hfac] at hval
            by_cases ht2 : 2 ≤ t
            · have hge : i ≤ t.minFac := by
                by_contra hc
                exact hfac ⟨ht2, by omega⟩
              by_cases heq : t.minFac = i
              · have hdvd : i ∣ t := heq ▸ Nat.minFac_dvd t
                have hsq : i * i ≤ t := sq_le_of_minFac_eq ht2 heq (by omega)
                rw [if_pos ⟨hsq, Nat.dvd_sub hdvd (Dvd.intro i rfl), hval⟩,
                  if_pos ⟨ht2, by omega⟩, heq]
              · have hnot : ¬(i * i ≤ t ∧ i ∣ t - i * i ∧ spf[t] = 0) := by
                  rintro ⟨hsq, hdvd, -⟩
                  have hdvdt : i ∣ t := by
                    have : t = t - i * i + i * i := by omega
                    rw [this]
                    exact Nat.dvd_add hdvd (Dvd.intro i rfl)
                  have := Nat.minFac_le_of_dvd hprime.two_le hdvdt
                  omega
                rw [if_neg hnot, hval, if_neg (by omega)]
            · have hnot : ¬(i * i ≤ t ∧ i ∣ t - i * i ∧ spf[t] = 0) := by
                rintro ⟨hsq, -, -⟩
                nlinarith [h2]
              rw [if_neg hnot, hval, if_neg (by omega)]
      · show (primes.push i).toList = _
        rw [Array.toList_push, hlist, List.range_succ, List.filter_append]
        simp [hprime]
  | case2 spf primes i hle hcond ih =>
      intro h2 hfill hlist
      rw [Nat.max_eq_right (by omega)]
      have hnotprime : ¬i.Prime := by
        intro hp
        refine hcond ⟨h2, ?_⟩
        have hval := hfill i (by omega)
        rw [if_neg (by rw [(Nat.prime_def_minFac.mp hp).2]; omega)] at hval
        simp [hval]
      rw [Nat.max_eq_right (show i + 1 ≤ n + 1 by omega)] at ih
      refine ih (by omega) ?_ ?_
      · intro t ht
        rw [hfill t ht]
        have hequiv : (2 ≤ t ∧ t.minFac < i) ↔ (2 ≤ t ∧ t.minFac < i + 1) := by
          constructor
          · rintro ⟨ha, hb⟩
            exact ⟨ha, by omega⟩
          · rintro ⟨ha, hb⟩
            refine ⟨ha, ?_⟩
            rcases Nat.lt_or_ge t.minFac i with h | h
            · exact h
            · have heq : t.minFac = i := by omega
              exact absurd (heq ▸ Nat.minFac_prime (show t ≠ 1 by omega)) hnotprime
        simp only [hequiv]
      · show primes.toList = _
        rw [hlist, List.range_succ, List.filter_append]
        simp [hnotprime]
  | case3 spf primes i hgt =>
      intro h2 hfill hlist
      rw [Nat.max_eq_left (by omega)]
      exact ⟨hfill, hlist⟩

theorem factorsAux_one {n : Nat} (self : Sieve n) (fuel : Nat) :
    factorsAux self 1 fuel = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [factorsAux, dif_neg (by omega)]

/-- Dividing by the least prime factor and repeating gives the factorisation:
the factors multiply back, each is prime, none is smaller than the least prime
factor of the number, and they come out in increasing order. -/
theorem factorsAux_spec {n : Nat} (self : Sieve n)
    (hself : ∀ t (ht : t < n + 1), self.minFactor[t] = if 2 ≤ t then t.minFac else 0) :
    ∀ fuel i : Nat, 0 < i → i < n + 1 → i ≤ fuel →
      (factorsAux self i fuel).prod = i ∧ (∀ q ∈ factorsAux self i fuel, q.Prime) ∧
        (∀ q ∈ factorsAux self i fuel, i.minFac ≤ q) ∧
        (factorsAux self i fuel).Sorted (· ≤ ·) := by
  intro fuel
  induction fuel with
  | zero => intro i hi _ hfuel; omega
  | succ fuel ih =>
      intro i hi hin hfuel
      rw [factorsAux]
      by_cases h2 : 2 ≤ i
      · rw [dif_pos ⟨h2, hin⟩]
        have hp : self.minFactor[i]'hin = i.minFac := by rw [hself i hin, if_pos h2]
        have hpprime : (i.minFac).Prime := Nat.minFac_prime (by omega)
        have hdvd : i.minFac ∣ i := Nat.minFac_dvd i
        have hlt : i / i.minFac < i := Nat.div_lt_self (by omega) hpprime.one_lt
        have hpos : 0 < i / i.minFac :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpprime.pos
        obtain ⟨hprod, hall, hge, hsorted⟩ := ih (i / i.minFac) hpos (by omega) (by omega)
        rw [hp, if_neg (by have := hpprime.two_le; omega)]
        have htail : ∀ q ∈ factorsAux self (i / i.minFac) fuel, i.minFac ≤ q := by
          intro q hq
          rcases Nat.lt_or_ge (i / i.minFac) 2 with hsmall | hbig
          · have h1 : i / i.minFac = 1 := by omega
            rw [h1, factorsAux_one] at hq
            exact absurd hq (List.not_mem_nil)
          · have hmd : (i / i.minFac).minFac ∣ i :=
              Nat.dvd_trans (Nat.minFac_dvd _) (Nat.div_dvd_of_dvd hdvd)
            have := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le hmd
            exact Nat.le_trans this (hge q hq)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.prod_cons, hprod, Nat.mul_div_cancel' hdvd]
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hpprime
          · exact hall q hq
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Nat.le_refl _
          · exact htail q hq
        · exact List.sorted_cons.mpr ⟨htail, hsorted⟩
      · rw [dif_neg (by tauto)]
        simp only [List.prod_nil, List.not_mem_nil, false_implies, implies_true, and_true,
          List.sorted_nil]
        omega

end Impl

/-- `build` records the least prime factor of every number from `2` on. -/
theorem build_minFactor (n t : Nat) (ht : t < n + 1) :
    (build n).minFactor[t] = if 2 ≤ t then t.minFac else 0 := by
  have hfill : Impl.Filled n 2 (Vector.replicate (n + 1) 0) := by
    intro u hu
    rw [if_neg ?_]
    · simp
    · rintro ⟨h2, hlt⟩
      have := (Nat.minFac_prime (show u ≠ 1 by omega)).two_le
      omega
  have hlist : Impl.Listed 2 #[] := by unfold Impl.Listed; decide
  obtain ⟨hf, -⟩ := Impl.sieveFrom_spec n (Vector.replicate (n + 1) 0) #[] 2 (by omega)
    hfill hlist
  have := hf t ht
  show (Impl.sieveFrom n (Vector.replicate (n + 1) 0) #[] 2).1[t] = _
  rw [this]
  by_cases h2 : 2 ≤ t
  · rw [if_pos ⟨h2, by have := Nat.minFac_le (show 0 < t by omega); omega⟩, if_pos h2]
  · rw [if_neg (by tauto), if_neg h2]

/-- …and lists exactly the primes up to `n`, in increasing order. -/
theorem build_primes (n : Nat) :
    (build n).primes.toList = (List.range (n + 1)).filter fun p => decide p.Prime := by
  have hfill : Impl.Filled n 2 (Vector.replicate (n + 1) 0) := by
    intro u hu
    rw [if_neg ?_]
    · simp
    · rintro ⟨h2, hlt⟩
      have := (Nat.minFac_prime (show u ≠ 1 by omega)).two_le
      omega
  have hlist : Impl.Listed 2 #[] := by unfold Impl.Listed; decide
  obtain ⟨-, hl⟩ := Impl.sieveFrom_spec n (Vector.replicate (n + 1) 0) #[] 2 (by omega)
    hfill hlist
  show (Impl.sieveFrom n (Vector.replicate (n + 1) 0) #[] 2).2.toList = _
  rw [hl]
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have : n = 0 := by omega
    subst this
    decide
  · rw [Nat.max_eq_right (by omega)]

/-- A number up to `n` passes `isPrime` exactly when it is prime. -/
@[simp] theorem build_isPrime (n : Nat) (i : Fin (n + 1)) :
    (build n).isPrime i = true ↔ Nat.Prime i.val := by
  rw [isPrime, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Fin.getElem_fin,
    build_minFactor n i.val i.isLt, Nat.prime_def_minFac]
  constructor
  · rintro ⟨h2, heq⟩
    rw [if_pos h2] at heq
    exact ⟨h2, heq⟩
  · rintro ⟨h2, heq⟩
    exact ⟨h2, by rw [if_pos h2, heq]⟩

/-- `minFac` is the least prime factor. -/
theorem build_minFac (n : Nat) (i : Fin (n + 1)) (h2 : 2 ≤ i.val) :
    (build n).minFac i = i.val.minFac := by
  rw [minFac, Fin.getElem_fin, build_minFactor n i.val i.isLt, if_pos h2]

/-- The factors multiply back to the number… -/
theorem primeFactors_prod (n : Nat) (i : Fin (n + 1)) (hi : 0 < i.val) :
    ((build n).primeFactors i).toList.prod = i.val :=
  (Impl.factorsAux_spec (build n) (build_minFactor n) (i.val + 1) i.val hi i.isLt
    (by omega)).1

/-- …and every one of them is prime. -/
theorem primeFactors_prime (n : Nat) (i : Fin (n + 1)) (hi : 0 < i.val) {q : Nat}
    (hq : q ∈ (build n).primeFactors i) : q.Prime :=
  (Impl.factorsAux_spec (build n) (build_minFactor n) (i.val + 1) i.val hi i.isLt
    (by omega)).2.1 q (by simpa [primeFactors] using hq)

/-- …and they come out in increasing order. -/
theorem primeFactors_sorted (n : Nat) (i : Fin (n + 1)) (hi : 0 < i.val) :
    ((build n).primeFactors i).toList.Sorted (· ≤ ·) := by
  simpa [primeFactors] using
    (Impl.factorsAux_spec (build n) (build_minFactor n) (i.val + 1) i.val hi i.isLt
      (by omega)).2.2.2

/-- The prime powers multiply back to the number too. -/
theorem factorize_prod (n : Nat) (i : Fin (n + 1)) (hi : 0 < i.val) :
    (((build n).factorize i).toList.map fun pe => pe.1 ^ pe.2).prod = i.val := by
  rw [factorize]
  simpa [List.runLength_prod] using
    (Impl.factorsAux_spec (build n) (build_minFactor n) (i.val + 1) i.val hi i.isLt (by omega)).1

end Sieve
end NumberTheory

end Cplib
