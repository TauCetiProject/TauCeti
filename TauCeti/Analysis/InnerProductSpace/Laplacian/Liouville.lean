/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integrable nonnegative subharmonic functions

A nonnegative integrable `C²` function on a nontrivial finite-dimensional real inner product
space with nonnegative Laplacian is zero. The sub-mean-value inequality bounds its value by
its total integral divided by the volume of an arbitrarily large ball. This is useful for
vanishing arguments in which a squared norm is subharmonic and the original field is in `L²`.

The same inequality on unit balls shows that a nonnegative function which is subharmonic and
integrable outside a ball tends to zero at infinity
(`TauCeti.tendsto_cocompact_of_integrableOn_of_laplacian_nonneg`): its value is bounded by its
integral over a unit ball, which escapes to infinity. This turns `L¹` or `L²` information on the
end of a space into pointwise decay, as needed before a comparison principle can be applied.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Filter Topology Set

/-- A nonnegative integrable subharmonic `C²` function on a nontrivial Euclidean space is zero.
The measure can be any additive Haar measure. -/
theorem eq_zero_of_integrable_of_nonneg_of_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfi : Integrable f μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hΔ : ∀ x, 0 ≤ Δ f x) : f = 0 := by
  funext x
  apply le_antisymm _ (hf₀ x)
  by_contra! hx
  have hv : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have ht : Tendsto (fun r : ℝ ↦ r ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) * f x)
      atTop atTop :=
    ((tendsto_pow_atTop (ne_of_gt Module.finrank_pos)).atTop_mul_const hv).atTop_mul_const hx
  obtain ⟨r, hr, hbig⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (ht.eventually_gt_atTop (∫ y, f y ∂μ))).exists
  have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ)
    (x₀ := x) (R := r) hf.contDiffOn hf.continuous.continuousOn (fun y _ ↦ hΔ y)
  rw [μ.addHaar_real_ball_of_pos x hr] at hmean
  exact (hmean.trans (setIntegral_le_integral hfi (Filter.Eventually.of_forall hf₀))).not_gt hbig

/-- A nonnegative function which is `C²` with nonnegative Laplacian outside the closed ball of
radius `R`, and integrable there, tends to zero at infinity. The measure can be any additive Haar
measure. -/
theorem tendsto_cocompact_of_integrableOn_of_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {R : ℝ} (hf : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 f x)
    (hfi : IntegrableOn f {x | R < ‖x‖} μ) (hf₀ : ∀ x, R < ‖x‖ → 0 ≤ f x)
    (hΔ : ∀ x, R < ‖x‖ → 0 ≤ Δ f x) : Tendsto f (cocompact E) (𝓝 0) := by
  have hT (r : ℝ) : MeasurableSet {y : E | r < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  set g := {y : E | R < ‖y‖}.indicator f
  have hg : Integrable g μ := hfi.integrable_indicator (hT R)
  have hg₀ : ∀ y, 0 ≤ g y := fun y ↦ by
    by_cases hy : R < ‖y‖
    · simpa [g, hy] using hf₀ y hy
    · simp [g, hy]
  -- The integral of `g` outside the ball of radius `r` tends to zero as `r → ∞`.
  have htail : Tendsto (fun r : ℝ ↦ ∫ y in {y : E | r < ‖y‖}, g y ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun r ↦ {y : E | r < ‖y‖}.indicator g) (f := 0) (fun y ↦ ‖g y‖)
      (.of_forall fun r ↦ (hg.indicator (hT r)).aestronglyMeasurable)
      (.of_forall fun r ↦ .of_forall fun y ↦ norm_indicator_le_norm_self _ _) hg.norm
      (.of_forall fun y ↦ tendsto_const_nhds.congr' <|
        (eventually_gt_atTop ‖y‖).mono fun r hr ↦ by simp [not_lt.mpr hr.le])
    simpa [integral_indicator (hT _)] using h
  -- The sub-mean-value inequality on unit balls far out.
  have hV : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hbound : ∀ x : E, R + 1 < ‖x‖ →
      f x ≤ (μ.real (ball (0 : E) 1))⁻¹ * ∫ y in {y : E | ‖x‖ - 1 < ‖y‖}, g y ∂μ := by
    intro x hx
    have hfar : ∀ y ∈ closedBall x 1, ‖x‖ - 1 ≤ ‖y‖ := fun y hy ↦ by
      have := norm_sub_norm_le x y
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hy
      linarith
    have hsub : closedBall x 1 ⊆ {y : E | R < ‖y‖} := fun y hy ↦
      (by linarith [hfar y hy] : R < ‖y‖)
    have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ) (x₀ := x) (R := 1)
      (fun y hy ↦ (hf y (hsub (ball_subset_closedBall hy))).contDiffWithinAt)
      (fun y hy ↦ (hf y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hΔ y (hsub (ball_subset_closedBall hy)))
    rw [μ.addHaar_real_ball_of_pos x one_pos, one_pow, one_mul,
      setIntegral_congr_fun measurableSet_ball fun y hy ↦
        (indicator_of_mem (hsub (ball_subset_closedBall hy)) f).symm] at hmean
    have hmono : ∫ y in ball x 1, g y ∂μ ≤ ∫ y in {y : E | ‖x‖ - 1 < ‖y‖}, g y ∂μ :=
      setIntegral_mono_set hg.integrableOn (.of_forall hg₀) <| .of_forall fun y hy ↦ by
        have := norm_sub_norm_le x y
        have hy' : dist y x < 1 := hy
        rw [dist_eq_norm, norm_sub_rev] at hy'
        exact (by linarith : ‖x‖ - 1 < ‖y‖)
    rw [inv_mul_eq_div, le_div_iff₀ hV, mul_comm]
    exact hmean.trans hmono
  have hupper : Tendsto (fun x : E ↦ (μ.real (ball (0 : E) 1))⁻¹ *
      ∫ y in {y : E | ‖x‖ - 1 < ‖y‖}, g y ∂μ) (cocompact E) (𝓝 0) := by
    simpa only [Function.comp_def, sub_eq_add_neg, mul_zero] using
      (htail.comp (tendsto_atTop_add_const_right _ (-1)
        (tendsto_norm_cocompact_atTop (E := E)))).const_mul
        (μ.real (ball (0 : E) 1))⁻¹
  have hfar := (tendsto_norm_cocompact_atTop (E := E)).eventually_gt_atTop (R + 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (hfar.mono fun x hx ↦ hf₀ x (by linarith)) (hfar.mono hbound)

end TauCeti
