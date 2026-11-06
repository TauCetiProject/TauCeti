/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The logarithmic potential of the semicircle law

For the standard semicircle law `semicircleReal 0 1` on `[-2, 2]` the logarithmic potential
`x ↦ ∫ log |x - y| d(semicircleReal 0 1)(y)` equals `x ^ 2 / 4 - 1 / 2` on `[-2, 2]`. Hence the
effective potential `x ^ 2 / 2 - 2 ∫ log |x - y| dμ(y)` of the Gaussian beta gas is the constant `1`
on the support, which is the Euler–Lagrange equation characterizing the semicircle law as the
equilibrium measure.

## Main results

* `TauCeti.Probability.integrable_log_abs_sub_semicircleReal`: the logarithmic kernel is
  integrable against the semicircle law.
* `TauCeti.Probability.integral_log_abs_sub_semicircleReal`: the value `x ^ 2 / 4 - 1 / 2` on
  `[-2, 2]`.

## Implementation notes

Let `g z = ∫ (z - y)⁻¹ dμ(y)` be the Stieltjes transform, which satisfies `g² - z g + 1 = 0` and has
negative imaginary part in the upper half-plane. There the complex logarithmic potential
`H z = ∫ log (z - y) dμ(y)` has derivative `g`, and so does `z g / 2 - log g - 1 / 2`; the two agree
up to a constant, which vanishes at infinity. Taking real parts gives the potential in the upper
half-plane, and the quadratic equation identifies the boundary values of `g` on `(-2, 2)`, whose
modulus is `1` and whose real part is `x / 2`. The potential is continuous up to the real axis by
dominated convergence.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.6.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The standard semicircle law is dominated by `π⁻¹` times Lebesgue measure. -/
theorem semicircleReal_zero_one_le :
    semicircleReal 0 1 ≤ ENNReal.ofReal Real.pi⁻¹ • (volume : Measure ℝ) := by
  rw [semicircleReal_eq_withDensity 0 one_pos]
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [withDensity_apply _ hs, smul_apply, smul_eq_mul, ← setLIntegral_const]
  refine lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal ?_
  have h4 : Real.sqrt (4 * ((1 : ℝ≥0) : ℝ) - (y - 0) ^ 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : ((1 : ℝ≥0) : ℝ) = 1 := NNReal.coe_one
    rw [this]
    nlinarith [sq_nonneg (y - 0)]
  have hpi := Real.pi_pos
  calc (2 * Real.pi * ((1 : ℝ≥0) : ℝ))⁻¹ * Real.sqrt (4 * ((1 : ℝ≥0) : ℝ) - (y - 0) ^ 2)
      ≤ (2 * Real.pi * ((1 : ℝ≥0) : ℝ))⁻¹ * 2 := by gcongr
    _ = Real.pi⁻¹ := by simp

/-- The standard semicircle law is carried by `[-2, 2]`. -/
theorem ae_mem_Icc_semicircleReal_zero_one :
    ∀ᵐ y ∂semicircleReal 0 1, y ∈ Icc (-2 : ℝ) 2 := by
  filter_upwards [ae_mem_Icc_semicircleReal 0 1] with y hy
  simpa using hy

/-- The standard semicircle law has no atoms. -/
theorem semicircleReal_zero_one_singleton (x : ℝ) : semicircleReal 0 1 {x} = 0 := by
  have h := semicircleReal_zero_one_le {x}
  simp only [smul_apply, smul_eq_mul, Real.volume_singleton, mul_zero,
    nonpos_iff_eq_zero] at h
  exact h

/-- The logarithmic kernel `y ↦ log |x - y|` is integrable against the semicircle law. -/
theorem integrable_log_abs_sub_semicircleReal (x : ℝ) :
    Integrable (fun y : ℝ ↦ Real.log |x - y|) (semicircleReal 0 1) := by
  have hrestr : (semicircleReal 0 1).restrict (Icc (-2) 2) = semicircleReal 0 1 :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_Icc_semicircleReal_zero_one
  have hlog : IntervalIntegrable (fun y : ℝ ↦ Real.log (x - y)) volume (-2) 2 := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := x + 2) (b := x - 2)).comp_sub_left x
    simpa using h
  have hint : IntegrableOn (fun y : ℝ ↦ Real.log |x - y|) (Icc (-2) 2) volume := by
    simp only [Real.log_abs]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hlog
  have h1 : Integrable (fun y : ℝ ↦ Real.log |x - y|)
      (ENNReal.ofReal Real.pi⁻¹ • volume.restrict (Icc (-2 : ℝ) 2)) :=
    hint.smul_measure ENNReal.ofReal_ne_top
  rw [← hrestr]
  refine h1.mono_measure ?_
  rw [← Measure.restrict_smul]
  exact Measure.restrict_mono_measure semicircleReal_zero_one_le _

/-- The Stieltjes transform of the standard semicircle law. -/
private def m (z : ℂ) : ℂ := resolventTransform (semicircleReal 0 1) z

section UpperHalfPlane

variable {z : ℂ}

private theorem restrict_Icc_semicircleReal_zero_one :
    (semicircleReal 0 1).restrict (Icc (-2) 2) = semicircleReal 0 1 :=
  Measure.restrict_eq_self_of_ae_mem ae_mem_Icc_semicircleReal_zero_one

private theorem im_gt_of_mem_ball {w : ℂ} (hw : w ∈ Metric.ball z (z.im / 2)) :
    z.im / 2 < w.im := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at h
  have := neg_abs_le (w.im - z.im)
  linarith

private theorem norm_inv_sub_le (hz : 0 < z.im) {w : ℂ} (hw : w ∈ Metric.ball z (z.im / 2))
    (y : ℝ) : ‖((w - y)⁻¹ : ℂ)‖ ≤ 2 / z.im := by
  have h1 := im_gt_of_mem_ball hw
  have h2 : w.im ≤ ‖w - (y : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w - (y : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  rw [norm_inv]
  calc ‖w - (y : ℂ)‖⁻¹ ≤ (z.im / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 2 / z.im := by field_simp

private theorem mem_slitPlane_sub {w : ℂ} (hw : 0 < w.im) (y : ℝ) :
    (w - y : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using hw.ne'

private theorem continuous_log_sub {w : ℂ} (hw : 0 < w.im) :
    Continuous fun y : ℝ ↦ Complex.log (w - y) :=
  continuous_iff_continuousAt.2 fun y ↦
    ((by fun_prop : Continuous fun y : ℝ ↦ (w - y : ℂ)).continuousAt).clog (mem_slitPlane_sub hw y)

private theorem integrable_log_sub {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun y : ℝ ↦ Complex.log (w - y)) (semicircleReal 0 1) := by
  have h : IntegrableOn (fun y : ℝ ↦ Complex.log (w - y)) (Icc (-2) 2) (semicircleReal 0 1) :=
    (continuous_log_sub hw).continuousOn.integrableOn_compact isCompact_Icc
  rwa [IntegrableOn, restrict_Icc_semicircleReal_zero_one] at h

/-- The complex logarithmic potential is holomorphic in the upper half-plane, with derivative the
Cauchy transform `∫ (z - y)⁻¹`. -/
private theorem hasDerivAt_logPotential (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, Complex.log (w - y) ∂semicircleReal 0 1)
      (∫ y : ℝ, ((z - y)⁻¹ : ℂ) ∂semicircleReal 0 1) z := by
  have hr : 0 < z.im / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := semicircleReal 0 1)
    (F := fun (w : ℂ) (y : ℝ) ↦ Complex.log (w - y))
    (F' := fun (w : ℂ) (y : ℝ) ↦ ((w - y)⁻¹ : ℂ)) (x₀ := z)
    (bound := fun _ ↦ 2 / z.im) (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.of_forall fun w ↦
      (Complex.measurable_log.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_log_sub hz)
    (by fun_prop)
    (Filter.Eventually.of_forall fun y w hw ↦ norm_inv_sub_le hz hw y)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y w hw ↦ by
      have hw' : 0 < w.im := by have := im_gt_of_mem_ball hw; linarith
      have hd : HasDerivAt (fun w : ℂ ↦ w - (y : ℂ)) 1 w := (hasDerivAt_id w).sub_const (y : ℂ)
      simpa using HasDerivAt.clog hd (mem_slitPlane_sub hw' y))
  exact key.2

private theorem hasDerivAt_m (hz : 0 < z.im) : ∃ d, HasDerivAt m d z := by
  refine ⟨_, hasDerivAt_resolventTransform (μ := semicircleReal 0 1) z ?_⟩
  rintro ⟨x, -, hx⟩
  have := congrArg Complex.im hx
  simp at this
  linarith

private theorem m_quad (hz : 0 < z.im) : m z * m z + z * m z + 1 = 0 := by
  have h := resolventTransform_semicircleReal_quadratic_eq_zero (a := 0) (v := 1) (z := z) (by
    rintro ⟨x, -, hx⟩
    have := congrArg Complex.im hx
    simp at this
    linarith)
  simpa [m] using h

private theorem m_im_pos (hz : 0 < z.im) : 0 < (m z).im :=
  im_resolventTransform_pos (μ := semicircleReal 0 1) (IsProbabilityMeasure.ne_zero _) hz

end UpperHalfPlane

end TauCeti.Probability
