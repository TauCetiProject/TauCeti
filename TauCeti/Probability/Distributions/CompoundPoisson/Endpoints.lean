/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Support
public import TauCeti.Probability.Quantile.Map
import TauCeti.Probability.Distributions.Dirac

/-!
# Endpoints of compound Poisson quantiles

A compound Poisson law at positive rate has lower support endpoint zero when its jumps are
almost surely nonnegative, and minus infinity otherwise. Its upper endpoint is zero when its
jumps are almost surely nonpositive, and plus infinity otherwise. The empty sum supplies the
endpoint zero, while arbitrarily many repetitions of a negative or positive support point
make the corresponding endpoint infinite.

The theorems give these endpoints as one-sided limits of interior quantiles in `EReal`.
They include zero rate and jumps concentrated at zero, without moment, density, or lattice
assumptions. Reflection relates the two limits, including laws with atoms or gaps in support.
The native natural and integer versions apply these formulas after real casting. For natural
jumps the lower endpoint is always zero; the upper endpoint is infinite exactly when the rate
is positive and the jumps are not almost surely zero.

## References

* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University
  Press, 1999, §24 (supports of infinitely divisible distributions).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal Pointwise

namespace TauCeti.Probability

open Classical in
/-- Compound Poisson quantiles tend at zero to zero for nonnegative jumps or zero rate,
and to minus infinity otherwise. The limit is through positive probability levels. -/
theorem tendsto_quantile_compoundPoissonMeasure_nhdsGT_zero (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ ((compoundPoissonMeasure r μ).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (if r = 0 ∨ (∀ᵐ x ∂μ, 0 ≤ x) then 0 else ⊥)) := by
  classical
  by_cases hr : r = 0
  · simp only [hr, compoundPoissonMeasure_zero, true_or, ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [Measure.quantile_dirac 0 hu.1 hu.2.le]
  by_cases hμ : ∀ᵐ x ∂μ, 0 ≤ x
  · simp only [hμ, or_true, ite_true]
    apply Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos
    · rw [compoundPoissonMeasure_eq_sum]
      refine Measure.ae_sum_iff.2 fun n ↦ Measure.ae_smul_measure ?_ _
      exact Measure.ae_mem_convolutionPower_of_ae_mem measurableSet_Ici le_rfl
        (by rintro _ ⟨x, hx, y, hy, rfl⟩; exact add_nonneg hx hy) hμ n
    · intro x hx
      rw [cdf_eq_real]
      exact (Real.exp_pos _).trans_le
        ((exp_neg_le_compoundPoissonMeasure_real_singleton_zero r μ).trans
          (measureReal_mono (singleton_subset_iff.mpr hx.le)))
  · simp only [hr, hμ, or_self, ite_false]
    apply Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos
    intro x
    obtain ⟨y, hy, hy0⟩ : ∃ y ∈ μ.support, y < 0 := by
      by_contra! h
      exact hμ (by filter_upwards [μ.support_mem_ae] with y hy using h y hy)
    obtain ⟨n, hn⟩ := exists_nsmul_lt hy0 x
    apply Measure.cdf_pos_of_mem_support_of_lt _ ?_ hn
    simpa only [List.sum_replicate] using
      list_sum_mem_support_compoundPoissonMeasure hr (List.replicate n y)
        (by intro z hz; simpa only [(List.mem_replicate.mp hz).2] using hy)

open Classical in
/-- Compound Poisson quantiles tend at one to zero for nonpositive jumps or zero rate,
and to plus infinity otherwise. The limit is through probability levels below one. -/
theorem tendsto_quantile_compoundPoissonMeasure_nhdsLT_one (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ ((compoundPoissonMeasure r μ).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if r = 0 ∨ (∀ᵐ x ∂μ, x ≤ 0) then 0 else ⊤)) := by
  classical
  have h := Measure.tendsto_quantile_neg_nhdsLT_one
    (tendsto_quantile_compoundPoissonMeasure_nhdsGT_zero r (μ.map (fun x ↦ -x)))
  have hsign : (∀ᵐ x ∂μ.map (fun x ↦ -x), 0 ≤ x) ↔ ∀ᵐ x ∂μ, x ≤ 0 := by
    rw [ae_map_iff measurable_neg.aemeasurable measurableSet_Ici]
    simp
  simpa only [Measure.neg_def, map_neg_compoundPoissonMeasure, Measure.map_map
    measurable_neg measurable_neg, Function.comp_def, neg_neg, Measure.map_id', hsign, neg_ite,
    neg_zero, EReal.neg_bot] using h

/-- The real cast of a natural-valued compound Poisson law has lower quantile endpoint zero,
including zero rate and jumps concentrated at zero. -/
theorem tendsto_quantile_map_natCast_compoundPoissonMeasure_nhdsGT_zero
    (r : ℝ≥0) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ (((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)).quantile u :
      EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hf : Measurable (Nat.cast : ℕ → ℝ) := by fun_prop
  have hmap := map_compoundPoissonMeasure r μ (Nat.castAddMonoidHom ℝ) hf
  rw [Nat.coe_castAddMonoidHom] at hmap
  rw [hmap]
  have hnonneg : ∀ᵐ x ∂μ.map (Nat.cast : ℕ → ℝ), 0 ≤ x := by
    rw [ae_map_iff hf.aemeasurable measurableSet_Ici]
    exact ae_of_all _ fun n ↦ Nat.cast_nonneg n
  simpa only [hnonneg, or_true, ite_true] using
    tendsto_quantile_compoundPoissonMeasure_nhdsGT_zero r (μ.map (Nat.cast : ℕ → ℝ))

open Classical in
/-- The upper quantile endpoint for natural compound Poisson jumps is infinite unless the
rate is zero or the jumps are almost surely zero. -/
theorem tendsto_quantile_map_natCast_compoundPoissonMeasure_nhdsLT_one
    (r : ℝ≥0) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ (((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)).quantile u :
      EReal)) (𝓝[<] 1) (𝓝 (if r = 0 ∨ (∀ᵐ k ∂μ, k = 0) then 0 else ⊤)) := by
  have hf : Measurable (Nat.cast : ℕ → ℝ) := by fun_prop
  have hmap := map_compoundPoissonMeasure r μ (Nat.castAddMonoidHom ℝ) hf
  rw [Nat.coe_castAddMonoidHom] at hmap
  rw [hmap]
  simpa only [ae_map_iff hf.aemeasurable measurableSet_Iic, Nat.cast_nonpos]
    using tendsto_quantile_compoundPoissonMeasure_nhdsLT_one r (μ.map (Nat.cast : ℕ → ℝ))

open Classical in
/-- After real casting, integer compound Poisson jumps have lower endpoint zero when they
are almost surely nonnegative or the rate is zero, and minus infinity otherwise. -/
theorem tendsto_quantile_map_intCast_compoundPoissonMeasure_nhdsGT_zero
    (r : ℝ≥0) (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ (((compoundPoissonMeasure r μ).map (Int.cast : ℤ → ℝ)).quantile u :
      EReal)) (𝓝[>] 0) (𝓝 (if r = 0 ∨ (∀ᵐ k ∂μ, 0 ≤ k) then 0 else ⊥)) := by
  have hf : Measurable (Int.cast : ℤ → ℝ) := by fun_prop
  have hmap := map_compoundPoissonMeasure r μ (Int.castAddHom ℝ) hf
  rw [Int.coe_castAddHom] at hmap
  rw [hmap]
  simpa only [ae_map_iff hf.aemeasurable measurableSet_Ici, Int.cast_nonneg_iff]
    using tendsto_quantile_compoundPoissonMeasure_nhdsGT_zero r (μ.map (Int.cast : ℤ → ℝ))

open Classical in
/-- After real casting, integer compound Poisson jumps have upper endpoint zero when they
are almost surely nonpositive or the rate is zero, and plus infinity otherwise. -/
theorem tendsto_quantile_map_intCast_compoundPoissonMeasure_nhdsLT_one
    (r : ℝ≥0) (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    Tendsto (fun u ↦ (((compoundPoissonMeasure r μ).map (Int.cast : ℤ → ℝ)).quantile u :
      EReal)) (𝓝[<] 1) (𝓝 (if r = 0 ∨ (∀ᵐ k ∂μ, k ≤ 0) then 0 else ⊤)) := by
  have hf : Measurable (Int.cast : ℤ → ℝ) := by fun_prop
  have hmap := map_compoundPoissonMeasure r μ (Int.castAddHom ℝ) hf
  rw [Int.coe_castAddHom] at hmap
  rw [hmap]
  simpa only [ae_map_iff hf.aemeasurable measurableSet_Iic, Int.cast_nonpos]
    using tendsto_quantile_compoundPoissonMeasure_nhdsLT_one r (μ.map (Int.cast : ℤ → ℝ))

end TauCeti.Probability
