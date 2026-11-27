/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

import Mathlib.Analysis.Convex.Combination

/-!
# Archimedean sizes of a principal different

The root discriminant is the weighted geometric mean of the archimedean absolute values
of a generator of the different. In a totally complex field all the weights are two, so
an unweighted product suffices. Both the multiplicative and logarithmic forms transfer
uniform placewise bounds to the root discriminant, without selecting representatives of
infinite places.

The totally complex product and the comparison up to twice the logarithmic error are used in
`New.Parameters.prod_deltaE_eq_rootDiscr_pow` and
`New.Parameters.abs_log_deltaE_sub_log_rootDiscr_le` of lsernau/grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open Finset Module NumberField NumberField.InfinitePlace Real Set

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The multiplicity-weighted product at infinity for a different generator is the root
discriminant raised to the field degree. -/
theorem prod_different_generator_pow_mult_eq_rootDiscr_pow {δ : 𝓞 K}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ}) :
    (∏ v : InfinitePlace K, v (δ : K) ^ v.mult) = rootDiscr K ^ finrank ℚ K := by
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  calc
    (∏ v : InfinitePlace K, v (δ : K) ^ v.mult) = |(discr K : ℝ)| := by
      rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
      have hnorm := absNorm_differentIdeal K (𝓞 K)
      rw [hδ, Ideal.absNorm_span_singleton] at hnorm
      have h : |Algebra.norm ℤ δ| = |discr K| := by simp only [Int.abs_eq_natAbs, hnorm]
      exact_mod_cast h
    _ = rootDiscr K ^ finrank ℚ K := by
      rw [rootDiscr_def, Int.cast_abs, ← rpow_natCast, rpow_inv_rpow (abs_nonneg _) hn]

/-- In a totally complex field, the product of the absolute values of a different generator
is the root discriminant to the power of the number of infinite places. -/
theorem prod_different_generator_eq_rootDiscr_pow [IsTotallyComplex K] {δ : 𝓞 K}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ}) :
    (∏ v : InfinitePlace K, v (δ : K)) = rootDiscr K ^ Fintype.card (InfinitePlace K) := by
  have hprod := prod_different_generator_pow_mult_eq_rootDiscr_pow hδ
  simp only [IsTotallyComplex.mult_eq, Finset.prod_pow] at hprod
  have hdegree : finrank ℚ K = Fintype.card (InfinitePlace K) * 2 := by
    simpa [IsTotallyComplex.mult_eq] using (sum_mult_eq (K := K)).symm
  have hr : 0 ≤ rootDiscr K := by rw [rootDiscr_def, Int.cast_abs]; positivity
  have hp : 0 ≤ ∏ v : InfinitePlace K, v (δ : K) := prod_nonneg fun v _ ↦ apply_nonneg v _
  apply (pow_left_inj₀ hp (pow_nonneg hr _) two_ne_zero).mp
  rwa [← pow_mul, ← hdegree]

/-- The logarithm of the root discriminant is the archimedean weighted average of the
logarithmic sizes of a different generator, with weight two at complex places. -/
theorem log_rootDiscr_eq_sum_mult_mul_log_div_finrank {δ : 𝓞 K}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ}) :
    log (rootDiscr K) = (∑ v : InfinitePlace K, (v.mult : ℝ) * log (v (δ : K))) /
      (finrank ℚ K : ℝ) := by
  have hδ0 : δ ≠ 0 := by
    intro he
    apply differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
    simpa [he] using hδ
  have hv (v : InfinitePlace K) : v (δ : K) ≠ 0 :=
    (InfinitePlace.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr hδ0)).ne'
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℚ) (M := K)).ne'
  have h := congrArg log (prod_different_generator_pow_mult_eq_rootDiscr_pow hδ)
  rw [log_prod (fun v _ ↦ pow_ne_zero _ (hv v))] at h
  simp only [log_pow] at h
  rw [eq_div_iff hn, mul_comm, h]

/-- Any common interval for the logarithmic sizes of a different generator also contains
the logarithm of the root discriminant. -/
theorem log_rootDiscr_mem_Icc_of_different_generator {δ : 𝓞 K} {a b : ℝ}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ})
    (h : ∀ v : InfinitePlace K, log (v (δ : K)) ∈ Icc a b) :
    log (rootDiscr K) ∈ Icc a b := by
  have hsum : ∑ v : InfinitePlace K, (v.mult : ℝ) = (finrank ℚ K : ℝ) := by
    exact_mod_cast sum_mult_eq (K := K)
  have hpos : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast finrank_pos (R := ℚ) (M := K)
  simpa [Finset.centerMass, hsum, div_eq_inv_mul, smul_eq_mul,
    log_rootDiscr_eq_sum_mult_mul_log_div_finrank hδ]
    using (convex_Icc a b).centerMass_mem (t := Finset.univ)
      (w := fun v : InfinitePlace K ↦ (v.mult : ℝ)) (z := fun v ↦ log (v (δ : K)))
      (fun _ _ ↦ Nat.cast_nonneg _) (hsum.symm ▸ hpos) (fun v _ ↦ h v)

/-- If all logarithmic sizes of a different generator lie within `C` of a common center,
they differ from the logarithm of the root discriminant by at most `2 * C`. -/
theorem abs_log_sub_log_rootDiscr_le_of_different_generator {δ : 𝓞 K} {a C : ℝ}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ})
    (h : ∀ v : InfinitePlace K, |log (v (δ : K)) - a| ≤ C) (v : InfinitePlace K) :
    |log (v (δ : K)) - log (rootDiscr K)| ≤ 2 * C := by
  have hmem : ∀ w : InfinitePlace K, log (w (δ : K)) ∈ Icc (a - C) (a + C) := by
    intro w
    obtain ⟨hl, hu⟩ := abs_le.mp (h w)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hl, hu⟩ := log_rootDiscr_mem_Icc_of_different_generator hδ hmem
  obtain ⟨hvl, hvu⟩ := hmem v
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Common bounds for the absolute values of a different generator also bound the root
discriminant. The lower endpoint need not be positive. -/
theorem rootDiscr_mem_Icc_of_different_generator {δ : 𝓞 K} {a b : ℝ}
    (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ})
    (h : ∀ v : InfinitePlace K, v (δ : K) ∈ Icc a b) : rootDiscr K ∈ Icc a b := by
  have hr : 0 ≤ rootDiscr K := by rw [rootDiscr_def, Int.cast_abs]; positivity
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hb : 0 ≤ b := (apply_nonneg v _).trans (h v).2
  have hn := (finrank_pos (R := ℚ) (M := K)).ne'
  have hpow := prod_different_generator_pow_mult_eq_rootDiscr_pow hδ
  refine ⟨?_, (pow_le_pow_iff_left₀ hr hb hn).mp ?_⟩
  · rcases le_or_gt a 0 with ha | ha
    · exact ha.trans hr
    apply (pow_le_pow_iff_left₀ ha.le hr hn).mp
    rw [← hpow, ← sum_mult_eq, ← prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ pow_nonneg ha.le _)
      (fun w _ ↦ pow_le_pow_left₀ ha.le (h w).1 _)
  · rw [← hpow, ← sum_mult_eq, ← prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (apply_nonneg w _) _)
      (fun w _ ↦ pow_le_pow_left₀ (apply_nonneg w _) (h w).2 _)

end TauCeti.NumberField
