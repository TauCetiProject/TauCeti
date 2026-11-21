/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Moments
public import TauCeti.MeasureTheory.Group.Integral

/-!
# Quadratic forms against radial weights

Averaging a bilinear form on the diagonal over a sphere replaces it by its orthonormal trace
divided by the dimension. Polar integration therefore reduces a quadratic form against a radial
weight on a ball to a scalar second moment, for any additive Haar measure and any centre.
No symmetry or sign condition on the form is needed.
This is useful for integrating quadratic Taylor terms against radial test functions.

The spherical calculation uses the mixed second moments of the uniform sphere law, and the
ball calculation uses `TauCeti.setIntegral_ball_zero_eq_integral_Ioo`.
-/

public section

noncomputable section

open MeasureTheory Metric Set Module
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ι : Type*} [Fintype ι]

/-- The surface integral of a bilinear form on the diagonal is the surface area times its
orthonormal trace divided by the dimension. -/
theorem integral_toSphere_bilinear_self (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∫ x : sphere (0 : E) 1, B (x : E) (x : E) ∂(volume : Measure E).toSphere =
      (volume : Measure E).toSphere.real univ *
        ((∑ i, B (b i) (b i)) / (finrank ℝ E : ℝ)) := by
  have h := Probability.integral_bilinear_self_uniformSphereMeasure b B
  rw [Probability.uniformSphereMeasure_def, integral_smul_measure, ENNReal.toReal_inv,
    smul_eq_mul] at h
  have hs : (volume : Measure E).toSphere.real univ ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr
      ⟨Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume), measure_ne_top _ _⟩
  exact (inv_mul_eq_iff_eq_mul₀ hs).mp h

/-- A continuous radial weight on a ball averages the quadratic part of a bilinear form to
its orthonormal trace. The radius may be arbitrary, including nonpositive radii. -/
theorem setIntegral_ball_bilinear_self_mul_radial (μ : Measure E) [μ.IsAddHaarMeasure]
    (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (a : E) {w : ℝ → ℝ} {R : ℝ}
    (hw : ContinuousOn w (Icc 0 (max R 0))) :
    ∫ x in ball a R, B (x - a) (x - a) * w ‖x - a‖ ∂μ =
      ((∑ i, B (b i) (b i)) / (finrank ℝ E : ℝ)) *
        ∫ x in ball a R, ‖x - a‖ ^ 2 * w ‖x - a‖ ∂μ := by
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add _ a R,
    setIntegral_ball_eq_setIntegral_ball_zero_add _ a R]
  simp only [add_sub_cancel_right]
  rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  simp only [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def,
    smul_eq_mul]
  suffices h : ∫ x in ball (0 : E) R, B x x * w ‖x‖ =
      ((∑ i, B (b i) (b i)) / (finrank ℝ E : ℝ)) *
        ∫ x in ball (0 : E) R, ‖x‖ ^ 2 * w ‖x‖ by rw [h]; ring
  have hcont : ContinuousOn (fun x : E ↦ w ‖x‖) (closedBall 0 R) :=
    hw.comp continuous_norm.continuousOn fun x hx ↦
      ⟨norm_nonneg _, (mem_closedBall_zero_iff.mp hx).trans (le_max_left _ _)⟩
  have hB : IntegrableOn (fun x : E ↦ B x x * w ‖x‖) (ball 0 R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R)
      ((B.continuous.clm_apply continuous_id).continuousOn.mul hcont)).mono_set
        ball_subset_closedBall
  have hn : IntegrableOn (fun x : E ↦ ‖x‖ ^ 2 * w ‖x‖) (ball 0 R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R)
      ((continuous_norm.pow 2).continuousOn.mul hcont)).mono_set ball_subset_closedBall
  rw [setIntegral_ball_zero_eq_integral_Ioo hB,
    setIntegral_ball_zero_eq_integral_Ioo hn, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hnorm (u : sphere (0 : E) 1) : ‖r • (u : E)‖ = r := by
    simp [norm_smul, Real.norm_of_nonneg hr.1.le]
  simp_rw [hnorm, map_smul, smul_apply, smul_eq_mul]
  have hfactor : (fun u : sphere (0 : E) 1 ↦ r * (r * B (u : E) (u : E)) * w r) =
      (fun u : sphere (0 : E) 1 ↦ (r ^ 2 * w r) * B (u : E) (u : E)) := by funext u; ring
  rw [hfactor, integral_const_mul, integral_toSphere_bilinear_self b B, integral_const]
  simp only [smul_eq_mul, Measure.real]
  ring

end TauCeti
