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

end TauCeti
