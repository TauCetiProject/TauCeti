/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.NumberTheory.SelbergSieve
public import TauCeti.NumberTheory.ArithmeticFunction.EulerProduct
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Lower bounds for finite Selberg normalizers

The density and harmonic comparisons hold at every real cutoff. The logarithmic comparison
assumes a nonnegative cutoff.
The finite-prime argument is adapted from Arend Mellendijk's PNT+ Selberg bounds.

## Main results

* `MonoidHom.prod_sum_positive_prime_powers` expands finite prime-power sums over a squarefree
  integer, in an arbitrary commutative semiring and including exponent zero.
* `BoundingSieve.sum_nu_le_sum_selbergTerms` bounds the density sum for completely multiplicative
  densities, at every real cutoff.
* `BoundingSieve.sum_inv_le_sum_selbergTerms` and `BoundingSieve.log_le_sum_selbergTerms` use only
  reciprocal lower bounds on the relevant prime densities.

## References

Adapted from Arend Mellendijk, PNT+, SelbergBounds.lean, the finite-product and normalizer bounds:
Repository: https://github.com/TauCetiProject/PrimeNumberTheoremAnd
Revision: e1ed50ef52b80922d0cf26293cdc74b84039b5d6
File: PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean

-/

public section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace BoundingSieve

private theorem nu_nonneg_of_dvd_pow (s : BoundingSieve)
    (hMul : ∀ a b, s.nu (a * b) = s.nu a * s.nu b) {n M : ℕ}
    (hn : n ∣ s.prodPrimes ^ M) : 0 ≤ s.nu n := by
  let F : ℕ →* ℝ := { toFun := s.nu, map_one' := s.nu_mult.1, map_mul' := hMul }
  have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero
    (pow_ne_zero M s.prodPrimes_ne_zero) hn
  rw [s.nu_mult.multiplicative_factorization _ hn0,
    prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_nonneg
  intro p hp
  change 0 ≤ F (p ^ n.factorization p)
  rw [map_pow]
  apply pow_nonneg
  have hpp := prime_of_mem_primeFactors hp
  exact (s.nu_pos_of_prime p hpp
    (hpp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hp).trans hn))).le

private theorem mem_prime_support_partition (s : BoundingSieve) (z : ℝ)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → p ∣ s.prodPrimes) {m : ℕ}
    (hm : m ∈ Icc 1 ⌊z⌋₊) :
    m ∈ (s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ z)).biUnion
      (fun d ↦ (d ^ ⌊z⌋₊).divisors.filter (d ∣ ·)) := by
  have hm' := mem_Icc.mp hm
  have hm0 : 0 < m := hm'.1
  have hz : 1 ≤ z := (Nat.one_le_floor_iff z).mp (hm'.1.trans hm'.2)
  have hmz : (m : ℝ) ≤ z := (Nat.le_floor_iff (zero_le_one.trans hz)).mp hm'.2
  let d := ∏ p ∈ m.primeFactors, p
  have hd : d ∣ s.prodPrimes := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (prime_of_mem_primeFactors hp).prime
    · intro p hp
      apply hP p (prime_of_mem_primeFactors hp)
      have hpm : (p : ℝ) ≤ m := by exact_mod_cast Nat.le_of_mem_primeFactors hp
      exact hpm.trans hmz
  have hdm : d ∣ m := Nat.prod_primeFactors_dvd m
  have hdmle : (d : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm0 hdm
  have hdle : (d : ℝ) ≤ z := hdmle.trans hmz
  have hdsq : Squarefree d := Nat.squarefree_prod_primeFactors m
  exact mem_biUnion.mpr ⟨d,
    mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, s.prodPrimes_ne_zero⟩, hdle⟩,
    mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.dvd_prod_primeFactors_pow_self hm0.ne').trans (pow_dvd_pow d hm'.2),
        pow_ne_zero _ hdsq.ne_zero⟩, hdm⟩⟩

private theorem sum_nu_le_partition (s : BoundingSieve) (z : ℝ)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → p ∣ s.prodPrimes)
    (hMul : ∀ a b, s.nu (a * b) = s.nu a * s.nu b) :
    ∑ m ∈ Icc 1 ⌊z⌋₊, s.nu m ≤
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ z),
        ∑ m ∈ (d ^ ⌊z⌋₊).divisors.filter (d ∣ ·), s.nu m := by
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg (fun m hm ↦ mem_prime_support_partition s z hP hm)
    intro m hm _
    obtain ⟨d, hd, hm⟩ := mem_biUnion.mp hm
    have hdP := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
    have hmd := Nat.dvd_of_mem_divisors (mem_filter.mp hm).1
    exact nu_nonneg_of_dvd_pow s hMul
      (hmd.trans (pow_dvd_pow_of_dvd hdP ⌊z⌋₊))
  · intro i hi j hj hij
    exact Nat.pairwiseDisjoint_divisors_pow_filter_dvd s.prodPrimes_squarefree.isRadical ⌊z⌋₊
      (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij

private theorem sum_divisors_prime_support_le_terms (s : BoundingSieve)
    (hMul : ∀ a b, s.nu (a * b) = s.nu a * s.nu b) (k d : ℕ)
    (hd : d ∣ s.prodPrimes) :
    ∑ m ∈ (d ^ (k + 1)).divisors.filter (d ∣ ·), s.nu m ≤ s.selbergTerms d := by
  let F : ℕ →* ℝ := { toFun := s.nu, map_one' := s.nu_mult.1, map_mul' := hMul }
  have hdsq := s.squarefree_of_dvd_prodPrimes hd
  change ∑ m ∈ (d ^ (k + 1)).divisors.filter (d ∣ ·), F m ≤ _
  rw [← MonoidHom.prod_sum_positive_prime_powers F (k + 1) d hdsq, selbergTerms_apply]
  apply MonoidHom.prod_sum_prime_powers_le F (k + 1) d hdsq
  · intro p hp
    exact (s.nu_pos_of_prime p (prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hd)).le
  · intro p hp
    exact s.nu_lt_one_of_prime p (prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hd)

/-- Complete multiplicativity compares the density sum with the finite Selberg normalizer.
The cutoff is an arbitrary real number; negative cutoffs give empty sums. -/
theorem sum_nu_le_sum_selbergTerms (s : BoundingSieve) (z : ℝ)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → p ∣ s.prodPrimes)
    (hMul : ∀ a b, s.nu (a * b) = s.nu a * s.nu b) :
    ∑ m ∈ Icc 1 ⌊z⌋₊, s.nu m ≤
      ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0 := by
  rw [← Finset.sum_filter]
  by_cases hz : 1 ≤ z
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (ne_of_gt ((Nat.one_le_floor_iff z).mpr hz))
    calc
      _ ≤ ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ z),
          ∑ m ∈ (d ^ ⌊z⌋₊).divisors.filter (d ∣ ·), s.nu m :=
        sum_nu_le_partition s z hP hMul
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        rw [hk]
        exact sum_divisors_prime_support_le_terms s hMul k d
          (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  · rw [Nat.floor_eq_zero.mpr (not_le.mp hz)]
    simp only [Icc_eq_empty_of_lt (by decide : 0 < 1), sum_empty]
    exact Finset.sum_nonneg fun d hd ↦
      (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le

private noncomputable def reciprocalDensity (s : BoundingSieve) : BoundingSieve :=
  { s with
    nu := ⟨fun n ↦ (n : ℝ)⁻¹, by simp⟩
    nu_mult := ⟨by simp, by intro a b _; simp [Nat.cast_mul, mul_comm]⟩
    nu_pos_of_prime := by intro p hp _; exact inv_pos.mpr (Nat.cast_pos.mpr hp.pos)
    nu_lt_one_of_prime := by
      intro p hp _
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt) }

/-- On squarefree sieve-supported indices, increasing nonnegative prime densities increases
`selbergTerms`. The comparison density need not have the same prime support. -/
theorem selbergTerms_le_of_prime_le (s t : BoundingSieve) (d : ℕ)
    (hs : d ∣ s.prodPrimes) (ht : ∀ p ∈ d.primeFactors, 0 ≤ t.nu p)
    (hnu : ∀ p ∈ d.primeFactors, t.nu p ≤ s.nu p) :
    t.selbergTerms d ≤ s.selbergTerms d := by
  have htprod : t.nu d = ∏ p ∈ d.primeFactors, t.nu p := by
    rw [← t.nu_mult.map_prod_of_subset_primeFactors d _ subset_rfl,
      Nat.prod_primeFactors_of_squarefree (s.squarefree_of_dvd_prodPrimes hs)]
  simp only [selbergTerms_apply, ← prod_primeFactors_nu hs, htprod,
    ← Finset.prod_mul_distrib, ← div_eq_mul_inv]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact div_nonneg (ht p hp)
      (sub_nonneg.mpr ((hnu p hp).trans
        (s.nu_lt_one_of_prime p (prime_of_mem_primeFactors hp)
          ((Nat.dvd_of_mem_primeFactors hp).trans hs)).le))
  · intro p hp
    exact div_le_div₀
      (s.nu_pos_of_prime p (prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hs)).le
      (hnu p hp)
      (sub_pos.mpr (s.nu_lt_one_of_prime p (prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hs)))
      (sub_le_sub_left (hnu p hp) 1)

/-- Prime densities at least `1 / p` give a harmonic lower bound for the normalizer.
Only prime values at or below the cutoff matter; no complete multiplicativity is assumed. -/
theorem sum_inv_le_sum_selbergTerms (s : BoundingSieve) (z : ℝ)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → p ∣ s.prodPrimes)
    (hnu : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → (p : ℝ)⁻¹ ≤ s.nu p) :
    ∑ m ∈ Icc 1 ⌊z⌋₊, (m : ℝ)⁻¹ ≤
      ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0 := by
  let t := reciprocalDensity s
  calc
    _ = ∑ m ∈ Icc 1 ⌊z⌋₊, t.nu m := rfl
    _ ≤ ∑ d ∈ t.prodPrimes.divisors, if (d : ℝ) ≤ z then t.selbergTerms d else 0 :=
      sum_nu_le_sum_selbergTerms t z hP (by intro a b; simp [t, reciprocalDensity, mul_comm])
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with hdz
      · apply selbergTerms_le_of_prime_le s t d (Nat.dvd_of_mem_divisors hd)
          (by intro p _; exact inv_nonneg.mpr (Nat.cast_nonneg p))
        intro p hp
        apply hnu p (prime_of_mem_primeFactors hp)
        have hpd : (p : ℝ) ≤ d := by exact_mod_cast Nat.le_of_mem_primeFactors hp
        exact hpd.trans hdz
      · rfl

/-- The finite Selberg normalizer is at least the logarithm of any nonnegative cutoff
whose primes are in the sieve and have density at least the reciprocal prime. -/
theorem log_le_sum_selbergTerms (s : BoundingSieve) (z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → p ∣ s.prodPrimes)
    (hnu : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → (p : ℝ)⁻¹ ≤ s.nu p) :
    Real.log z ≤
      ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0 := by
  refine (log_le_harmonic_floor z hz).trans ?_
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
    sum_inv_le_sum_selbergTerms s z hP hnu

end BoundingSieve
