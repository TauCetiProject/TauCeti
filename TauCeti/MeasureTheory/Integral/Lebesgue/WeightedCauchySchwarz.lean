/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Weighted Cauchy–Schwarz with a change of variables

An overlap integral between two cutoffs is bounded by two weighted energies. A common density
can include both cutoff factors, so the cutoffs need not be indicators. A measure-preserving
equivalence puts the second energy in the coordinates of the second cutoff, where it carries
the reciprocal weight.

The change-of-variables formulation follows the weighted estimate in
`New.Filling.amplitudeMajorant_sq_le` of `grh/src/New/Spanning/RemainingTerms/SchurTest.lean` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- Weighted Cauchy–Schwarz for extended nonnegative functions. The weight must be positive
and finite only where the product is nonzero, almost everywhere. -/
theorem lintegral_mul_sq_le_weighted {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g w : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hw : AEMeasurable w μ) (hw' : ∀ᵐ x ∂μ, f x * g x ≠ 0 → w x ≠ 0 ∧ w x ≠ ∞) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤
      (∫⁻ x, f x ^ 2 * w x ∂μ) * (∫⁻ x, g x ^ 2 / w x ∂μ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le (p := 1 / 2) (q := 1 / 2)
    ((hf.pow_const (2 : ℕ)).mul hw) ((hg.pow_const (2 : ℕ)).div hw)
    (by norm_num) (by norm_num) (by norm_num)
  have hhalf (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have heq : (fun x ↦ (f x ^ 2 * w x) ^ (1 / 2 : ℝ) * (g x ^ 2 / w x) ^ (1 / 2 : ℝ))
      =ᵐ[μ] fun x ↦ f x * g x := by
    filter_upwards [hw'] with x hx
    by_cases hfg : f x * g x = 0
    · rcases mul_eq_zero.mp hfg with h | h <;> simp [h, div_eq_mul_inv]
    · obtain ⟨h₀, htop⟩ := hx hfg
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), div_eq_mul_inv,
        mul_mul_mul_comm (f x ^ 2) (w x), ENNReal.mul_inv_cancel h₀ htop, mul_one, ← mul_pow, hsq]
  simp only [Pi.mul_apply, Pi.div_apply] at h
  rw [lintegral_congr_ae heq] at h
  simpa only [mul_pow, hhalf] using pow_le_pow_left' h 2

/-- Weighted Cauchy–Schwarz for an overlap along a measure-preserving equivalence.
All three integrals use the common density `d`. The second energy is over the reversed overlap,
with both the density and the reciprocal weight transported by the inverse equivalence. -/
theorem _root_.MeasureTheory.MeasurePreserving.setLIntegral_mul_comp_sq_le_weighted
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {e : α ≃ᵐ β} (he : MeasurePreserving e μ ν) {s : Set α} {t : Set β}
    {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} {d w : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.restrict (s ∩ e ⁻¹' t)))
    (hg : AEMeasurable g (ν.restrict (t ∩ e.symm ⁻¹' s)))
    (hd : AEMeasurable d (μ.restrict (s ∩ e ⁻¹' t)))
    (hw : AEMeasurable w (μ.restrict (s ∩ e ⁻¹' t)))
    (hw' : ∀ᵐ x ∂(μ.restrict (s ∩ e ⁻¹' t)).withDensity d,
      f x * g (e x) ≠ 0 → w x ≠ 0 ∧ w x ≠ ∞) :
    (∫⁻ x in s ∩ e ⁻¹' t, d x * (f x * g (e x)) ∂μ) ^ 2 ≤
      (∫⁻ x in s ∩ e ⁻¹' t, d x * (f x ^ 2 * w x) ∂μ) *
      (∫⁻ y in t ∩ e.symm ⁻¹' s, d (e.symm y) * (g y ^ 2 / w (e.symm y)) ∂ν) := by
  have hs : e ⁻¹' (t ∩ e.symm ⁻¹' s) = s ∩ e ⁻¹' t := by
    ext x
    simp [and_comm]
  have hp := he.restrict_preimage_emb e.measurableEmbedding (t ∩ e.symm ⁻¹' s)
  rw [hs] at hp
  have hg' : AEMeasurable (fun x ↦ g (e x)) (μ.restrict (s ∩ e ⁻¹' t)) :=
    (hp.aemeasurable_comp_iff e.measurableEmbedding).2 hg
  have hac := withDensity_absolutelyContinuous (μ.restrict (s ∩ e ⁻¹' t)) d
  have h := lintegral_mul_sq_le_weighted (hf.mono_ac hac) (hg'.mono_ac hac) (hw.mono_ac hac) hw'
  have hdensity {k : α → ℝ≥0∞} (hk : AEMeasurable k (μ.restrict (s ∩ e ⁻¹' t))) :
      ∫⁻ x, k x ∂(μ.restrict (s ∩ e ⁻¹' t)).withDensity d =
        ∫⁻ x in s ∩ e ⁻¹' t, d x * k x ∂μ := by
    simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul₀ hd hk
  rw [hdensity (k := fun x ↦ f x * g (e x)) (hf.mul hg'),
    hdensity (k := fun x ↦ f x ^ 2 * w x) ((hf.pow_const (2 : ℕ)).mul hw),
    hdensity (k := fun x ↦ g (e x) ^ 2 / w x) ((hg'.pow_const (2 : ℕ)).div hw)] at h
  have hcomp := hp.lintegral_comp_emb e.measurableEmbedding
    (fun y ↦ d (e.symm y) * (g y ^ 2 / w (e.symm y)))
  simp only [e.symm_apply_apply] at hcomp
  rwa [← hcomp]

end TauCeti
