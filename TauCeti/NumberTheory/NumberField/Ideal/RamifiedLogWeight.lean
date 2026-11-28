/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.NumberField.ResidueDegree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification-weighted logarithmic prime sums

Above a rational prime `p`, the local weights `e(v/p) log(N v) / [K : ℚ]` add up to `log p`.
Thus a finite sum of local gains that depend only on the prime below the place can be computed
as a sum over rational primes, even when the heights or colengths defining the gains come from
an auxiliary number field. No Galois assumption on that field is needed.
-/

public section

open Finset IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The ramification-weighted logarithmic norms of the primes above `p`, divided by the
field degree, sum to `log p`. -/
theorem finsum_ramificationIdx_mul_log_absNorm_of_rationalPrimeBelow {p : ℕ} (hp : p.Prime) :
    (∑ᶠ v ∈ {v : HeightOneSpectrum (𝓞 K) | rationalPrimeBelow v = p},
      (v.asIdeal.ramificationIdx ℤ : ℝ) * Real.log v.asIdeal.absNorm / Module.finrank ℚ K) =
      Real.log p := by
  classical
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hP : P.IsPrime := (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
  have : P.IsMaximal := hP.isMaximal hP0
  let inst := (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) P).fintype
  have hnorm : P.absNorm = p := by simp [P, Ideal.absNorm_span_singleton]
  have hdiv (v : HeightOneSpectrum (𝓞 K)) : rationalPrimeBelow v = p ↔
      v.asIdeal ∣ P.map (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.liesOver_iff_dvd_map v.isPrime.ne_top, Ideal.liesOver_iff]
    constructor
    · intro h
      symm
      rw [under_eq_span_rationalPrimeBelow, h]
    · intro h
      rw [rationalPrimeBelow_def, ← h, hnorm]
  let e := (Equiv.subtypeEquivRight hdiv).trans (HeightOneSpectrum.equivPrimesOver (𝓞 K) hP0)
  let instFiber := Fintype.ofEquiv _ e.symm
  have hdeg : (∑ q : P.primesOver (𝓞 K),
      (q.val.ramificationIdx ℤ : ℝ) * q.val.inertiaDeg ℤ) = Module.finrank ℚ K := by
    exact_mod_cast (Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K)).trans
      (RingOfIntegers.rank K)
  have hsum : (∑ v : {v : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow v = p},
      (v.val.asIdeal.ramificationIdx ℤ : ℝ) * v.val.asIdeal.inertiaDeg ℤ) =
      Module.finrank ℚ K := by
    rw [← hdeg]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, ← sum_div]
  calc
    _ = ((∑ v : {v : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow v = p},
        (v.val.asIdeal.ramificationIdx ℤ : ℝ) * v.val.asIdeal.inertiaDeg ℤ) * Real.log p) /
          Module.finrank ℚ K := by
      rw [sum_mul]
      congr 1
      refine sum_congr rfl fun v _ ↦ ?_
      rw [absNorm_eq_rationalPrimeBelow_pow, v.property, Nat.cast_pow, Real.log_pow, mul_assoc]
    _ = _ := by
      have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
        exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
      rw [hsum, mul_comm, mul_div_cancel_right₀ _ hd]

/-- Reindex a finite sum of ramification-weighted logarithmic norms with a coefficient depending
only on the prime below the place. The sum uses every prime of `𝓞 K` lying over `S`. -/
theorem finsum_ramificationIdx_mul_log_absNorm_over_rationalPrimes
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (g : ℕ → ℝ) :
    (∑ᶠ v ∈ {v : HeightOneSpectrum (𝓞 K) | rationalPrimeBelow v ∈ S},
      (v.asIdeal.ramificationIdx ℤ : ℝ) * Real.log v.asIdeal.absNorm / Module.finrank ℚ K *
        g (rationalPrimeBelow v)) = ∑ p ∈ S, Real.log p * g p := by
  classical
  let b := fun v : HeightOneSpectrum (𝓞 K) ↦ rationalPrimeBelow v
  let f := fun v : HeightOneSpectrum (𝓞 K) ↦
    (v.asIdeal.ramificationIdx ℤ : ℝ) * Real.log v.asIdeal.absNorm / Module.finrank ℚ K
  have hfinite (p : ℕ) (hp : p ∈ (S : Set ℕ)) : (b ⁻¹' {p}).Finite := by
    have hprime := hS p hp
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    refine (primesDividing K (p : ℤ) hp0).finite_toSet.subset ?_
    intro v hv
    have heq : rationalPrimeBelow v = p := hv
    rw [Finset.mem_coe, mem_primesDividing, heq]
  calc
    _ = ∑ᶠ v ∈ ⋃ p ∈ (S : Set ℕ), b ⁻¹' {p}, f v * g (b v) := by
      rw [Set.biUnion_preimage_singleton]
      rfl
    _ = ∑ p ∈ S, ∑ᶠ v ∈ b ⁻¹' {p}, f v * g (b v) := by
      rw [finsum_mem_biUnion (Set.pairwiseDisjoint_fiber b _) S.finite_toSet hfinite,
        finsum_mem_coe_finset]
    _ = _ := by
      refine sum_congr rfl fun p hp ↦ ?_
      rw [finsum_mem_congr rfl (fun v hv ↦ congrArg (fun t ↦ f v * g t)
        (Set.mem_singleton_iff.mp hv)), ← finsum_mem_mul']
      · exact congrArg (· * g p) <|
          finsum_ramificationIdx_mul_log_absNorm_of_rationalPrimeBelow (K := K) (hS p hp)
      · exact hfinite p hp

end TauCeti
