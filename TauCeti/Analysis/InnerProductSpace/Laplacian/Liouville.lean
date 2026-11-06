/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integrable nonnegative subharmonic functions

A nonnegative integrable `C²` function on a nontrivial finite-dimensional real inner product
space with nonnegative Laplacian is zero. The sub-mean-value inequality bounds its value by
its total integral divided by the volume of an arbitrarily large ball. This is useful for
vanishing arguments in which a squared norm is subharmonic and the original field is in `L²`.

The same inequality on unit balls shows that a nonnegative function which is subharmonic and
integrable only on the exterior of a ball tends to zero at infinity: its value at `x` is bounded
by its integral over the region `‖y‖ > ‖x‖ - 1`, divided by the volume of the unit ball. This
turns finite energy of a field into pointwise decay at infinity.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Filter Topology

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

/-- A function which is nonnegative, `C²`, subharmonic and integrable on the exterior `‖x‖ > R` of
a ball in a Euclidean space tends to zero at infinity. The measure can be any additive
Haar measure. -/
theorem tendsto_cocompact_of_integrableOn_of_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} {R : ℝ} (hf : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 f x)
    (hfi : IntegrableOn f {x | R < ‖x‖} μ) (hf₀ : ∀ x, R < ‖x‖ → 0 ≤ f x)
    (hΔ : ∀ x, R < ‖x‖ → 0 ≤ Δ f x) : Tendsto f (cocompact E) (𝓝 0) := by
  set v := μ.real (ball (0 : E) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  -- The integral of `f` over the region `‖y‖ > r` tends to zero as `r → ∞`.
  set g : ℝ → ℝ := fun r ↦ ∫ y in {y : E | r < ‖y‖}, f y ∂μ
  have hg : Tendsto g atTop (𝓝 0) := by
    have hlim := tendsto_setIntegral_of_antitone (μ := μ) (f := f)
      (s := fun r : ℝ ↦ {y : E | r < ‖y‖})
      (fun r ↦ measurableSet_lt measurable_const measurable_norm)
      (fun r r' hrr' y hy ↦ hrr'.trans_lt hy) ⟨R, hfi⟩
    have hempty : (⋂ r : ℝ, {y : E | r < ‖y‖}) = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy ↦
        lt_irrefl ‖y‖ (by simpa using Set.mem_iInter.mp hy ‖y‖)
    simpa [hempty] using hlim
  -- Far out, the sub-mean-value inequality on the unit ball bounds `f x` by `g (‖x‖ - 2) / v`.
  have hbound : ∀ x : E, R + 2 < ‖x‖ → f x ≤ g (‖x‖ - 2) / v := by
    intro x hx
    have hsub : closedBall x 1 ⊆ {y : E | ‖x‖ - 2 < ‖y‖} := fun y hy ↦ by
      have h₁ := norm_sub_norm_le x y
      have h₂ := mem_closedBall.mp hy
      rw [dist_eq_norm, norm_sub_rev] at h₂
      exact (by linarith : ‖x‖ - 2 < ‖y‖)
    have hext : {y : E | ‖x‖ - 2 < ‖y‖} ⊆ {y : E | R < ‖y‖} := fun y (hy : ‖x‖ - 2 < ‖y‖) ↦
      (by linarith : R < ‖y‖)
    have hin : ∀ y ∈ closedBall x 1, R < ‖y‖ := fun y hy ↦ hext (hsub hy)
    have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ) (x₀ := x) (R := 1)
      (fun y hy ↦ (hf y (hin y (ball_subset_closedBall hy))).contDiffWithinAt)
      (fun y hy ↦ (hf y (hin y hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hΔ y (hin y (ball_subset_closedBall hy)))
    rw [μ.addHaar_real_ball_center x 1] at hmean
    rw [le_div_iff₀ hv, mul_comm]
    exact hmean.trans (setIntegral_mono_set (hfi.mono_set hext)
      (ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_norm)
        fun y hy ↦ hf₀ y (hext hy))
      (ball_subset_closedBall.trans hsub).eventuallyLE)
  have hev : ∀ᶠ x in cocompact E, R + 2 < ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually_gt_atTop _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (hev.mono fun x hx ↦ hf₀ x (by linarith)) (hev.mono hbound)
  simpa [sub_eq_add_neg] using
    (hg.comp (tendsto_atTop_add_const_right _ (-2) tendsto_norm_cocompact_atTop)).div_const v

end TauCeti
