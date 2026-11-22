/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Log.Kernel
import TauCeti.Analysis.Complex.UpperHalfPlane.Cpow
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Logarithmic potentials of measures on the plane

The logarithmic potential of a finite measure `μ` is `z ↦ ∫ log ‖z - w‖ ∂μ(w)`.
Subtracting `log⁺ ‖w‖` inside the integral gives the normalized potential, whose local
`L²` bounds are uniform over probability measures, even when their supports are unbounded.
Both potentials recover the measure by the distributional Laplacian when the ordinary
potential has a finite logarithmic moment. The normalized potential works for any finite
measure.

For real measures embedded in the plane, the potential is the integral of the real-line
kernel. Compactly supported finite real measures have integrable off-axis kernels and a
complex logarithmic kernel integral whose derivative is minus the resolvent transform.
Bounded real probability measures admit affine transport and normalization at imaginary
infinity; at non-atomic points their vertical boundary values converge when the real kernel
is integrable.

The recovery formula is the measure-theoretic form of the identity in T. Tao,
*Topics in Random Matrix Theory*, §2.8.3. The single-pole identity used here is
`TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`.
-/

public section

namespace MeasureTheory.Measure

open Filter InnerProductSpace Laplacian Metric Set
open scoped ENNReal Real Topology

noncomputable section

/-- The logarithmic potential of a measure on the plane, formed with the Bochner integral.
The kernel uses Lean's value `Real.log 0 = 0`. For a finite measure with finite logarithmic
moment, the integral is defined for Lebesgue-almost every point, including for atomic measures. -/
def logarithmicPotential (μ : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂μ

/-- The logarithmic potential as an integral over the locations of the poles. -/
theorem logarithmicPotential_def (μ : Measure ℂ) (z : ℂ) :
    μ.logarithmicPotential z = ∫ w, Real.log ‖z - w‖ ∂μ := (rfl)

/-- The potential of a real measure embedded in the complex plane. -/
theorem logarithmicPotential_map_ofReal (μ : Measure ℝ) (z : ℂ) :
    (μ.map Complex.ofReal).logarithmicPotential z =
      ∫ x : ℝ, Real.log ‖z - x‖ ∂μ := by
  rw [logarithmicPotential_def, integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]

/-- The complex logarithmic kernel is integrable off the real axis for a finite real measure
carried by a compact set. -/
theorem integrable_clog_sub_of_im_ne_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ.restrict s = μ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun y : ℝ ↦ Complex.log (z - y)) μ := by
  have h : IntegrableOn (fun y : ℝ ↦ Complex.log (z - y)) s μ :=
    (TauCeti.continuous_log_sub_of_im_ne_zero hz).continuousOn.integrableOn_compact hs
  rwa [IntegrableOn, hμ] at h

/-- The logarithm of the norm of the kernel is integrable off the real axis for a finite real
measure carried by a compact set. -/
theorem integrable_log_norm_sub_of_im_ne_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ.restrict s = μ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun y : ℝ ↦ Real.log ‖z - y‖) μ := by
  have h := (integrable_clog_sub_of_im_ne_zero μ hs hμ hz).re
  refine h.congr ?_
  filter_upwards with y
  exact Complex.log_re _

/-- The real logarithmic kernel integral is the real part of the complex logarithmic kernel
integral off the real axis. -/
theorem integral_log_norm_sub_eq_re_of_im_ne_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ.restrict s = μ) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂μ) = (∫ y : ℝ, Complex.log (z - y) ∂μ).re := by
  calc
    ∫ y : ℝ, Real.log ‖z - y‖ ∂μ = ∫ y : ℝ, (Complex.log (z - y)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Complex.log_re]
    _ = (∫ y : ℝ, Complex.log (z - y) ∂μ).re :=
      integral_re (integrable_clog_sub_of_im_ne_zero μ hs hμ hz)

/-- The derivative of the complex logarithmic potential in the upper half-plane is minus
the resolvent transform of the real measure. -/
theorem hasDerivAt_integral_clog_sub_of_im_pos (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hs : IsCompact s) (hμ : μ.restrict s = μ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, Complex.log (w - y) ∂μ)
      (-MeasureTheory.resolventTransform μ z) z := by
  have hr : 0 < z.im / 2 := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun (w : ℂ) (y : ℝ) ↦ Complex.log (w - y))
    (F' := fun (w : ℂ) (y : ℝ) ↦ ((w - y)⁻¹ : ℂ)) (x₀ := z)
    (bound := fun _ ↦ 2 / z.im) (Metric.ball_mem_nhds z hr)
    (Filter.Eventually.of_forall fun w ↦
      (Complex.measurable_log.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_clog_sub_of_im_ne_zero μ hs hμ hz.ne')
    (by fun_prop)
    (Filter.Eventually.of_forall fun y w hw ↦ Complex.norm_sub_inv_le_of_mem_ball hw y)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y w hw ↦ by
      have hw' : 0 < w.im := by have := Complex.im_gt_of_mem_ball hw; linarith
      have hd : HasDerivAt (fun w : ℂ ↦ w - (y : ℂ)) 1 w := (hasDerivAt_id w).sub_const (y : ℂ)
      simpa using HasDerivAt.clog hd (TauCeti.sub_ofReal_mem_slitPlane_of_im_pos hw' y))
  convert key.2 using 1
  rw [MeasureTheory.resolventTransform_apply, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  simp only [resolvent, Ring.inverse_eq_inv, Complex.coe_algebraMap]
  rw [← neg_sub z (y : ℂ), inv_neg, neg_neg]

/-- A real measure dominated by a finite multiple of volume on a bounded interval has an
integrable logarithmic kernel at every real point. -/
theorem integrable_log_abs_sub_of_le_smul_volume_restrict (μ : Measure ℝ) (x l u : ℝ)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ : μ ≤ c • volume.restrict (Icc l u)) :
    Integrable (fun y : ℝ ↦ Real.log |x - y|) μ := by
  by_cases hlu : l ≤ u
  · have hlog : IntervalIntegrable (fun y : ℝ ↦ Real.log (x - y)) volume l u := by
      have h := (intervalIntegral.intervalIntegrable_log' (a := x - l) (b := x - u)).comp_sub_left x
      simpa using h
    have hint : IntegrableOn (fun y : ℝ ↦ Real.log |x - y|) (Icc l u) volume := by
      simp only [Real.log_abs]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hlu).1 hlog
    exact (hint.smul_measure hc).mono_measure hμ
  · have hμzero : μ = 0 := by
      apply le_antisymm ?_ (Measure.zero_le μ)
      simpa [Icc_eq_empty hlu] using hμ
    simp [hμzero]

/-- For a finite real measure of bounded support, vertical logarithmic kernels converge to the
real-axis kernel at a non-atomic point where the latter is integrable. -/
theorem tendsto_integral_log_norm_sub_of_ae_abs_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x R : ℝ) (hR : ∀ᵐ y ∂μ, |y| ≤ R) (hne : ∀ᵐ y ∂μ, y ≠ x)
    (hint : Integrable (fun y : ℝ ↦ Real.log |x - y|) μ) :
    Tendsto (fun ε : ℝ ↦ ∫ y : ℝ, Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂μ)
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, Real.log |x - y| ∂μ)) := by
  let bound : ℝ → ℝ := fun y ↦ ‖Real.log |x - y|‖ + Real.log (|x| + R + 1)
  have hbound_integrable : Integrable bound μ := by
    have hconst := integrable_const (Real.log (|x| + R + 1)) (μ := μ)
    simpa [bound, Real.norm_eq_abs] using hint.norm.add hconst
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_integrable ?_
  · refine Filter.Eventually.of_forall fun ε ↦ ?_
    have hmeas : Measurable fun y : ℝ ↦
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with ε hε hε1
    have hεpos : 0 < ε := hε
    have hεle : ε ≤ 1 := hε1.le
    filter_upwards [hR, hne] with y hy hxy
    simpa [bound] using
      Real.norm_log_norm_add_mul_I_sub_le_of_ne_of_abs_le x y ε R
        (by rw [abs_of_pos hεpos]; exact hεle) hy hxy
  · filter_upwards [hne] with y hxy
    exact TauCeti.tendsto_log_norm_add_mul_I_sub x y hxy

/-- On the imaginary axis, the logarithmic kernel integral of a bounded real probability
measure lies between `log t` and `log (t + R)`. -/
theorem integral_log_norm_mul_I_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : ∀ᵐ y ∂μ, |y| ≤ R) (t : ℝ) (ht : 0 < t) :
    Real.log t ≤ ∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂μ ∧
      (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂μ) ≤ Real.log (t + R) := by
  have hμ : μ.restrict (Icc (-R) R) = μ :=
    Measure.restrict_eq_self_of_ae_mem (hR.mono fun _ hy ↦ abs_le.mp hy)
  have hInt := integrable_log_norm_sub_of_im_ne_zero μ isCompact_Icc hμ
    (z := (t : ℂ) * Complex.I) (by simpa using ht.ne')
  have hlow : ∀ᵐ y : ℝ ∂μ, Real.log t ≤ Real.log ‖(t : ℂ) * Complex.I - y‖ := by
    filter_upwards with y
    apply Real.log_le_log ht
    have h := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - (y : ℂ))
    have him : (((t : ℂ) * Complex.I - y).im) = t := by simp
    rw [him] at h
    simpa [abs_of_pos ht] using h
  have hhigh : ∀ᵐ y : ℝ ∂μ,
      Real.log ‖(t : ℂ) * Complex.I - y‖ ≤ Real.log (t + R) := by
    filter_upwards [hR] with y hy
    have him : (((t : ℂ) * Complex.I - (y : ℂ)).im) = t := by simp
    have hnorm := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - (y : ℂ))
    rw [him] at hnorm
    have hnormpos : 0 < ‖(t : ℂ) * Complex.I - y‖ :=
      lt_of_lt_of_le ht (by simpa [abs_of_pos ht] using hnorm)
    apply Real.log_le_log hnormpos
    calc
      ‖(t : ℂ) * Complex.I - (y : ℂ)‖ ≤ ‖(t : ℂ) * Complex.I‖ + ‖(y : ℂ)‖ :=
        norm_sub_le _ _
      _ = t + |y| := by simp [abs_of_pos ht]
      _ ≤ t + R := add_le_add_right hy t
  constructor
  · simpa [integral_const] using integral_mono_ae (integrable_const (Real.log t)) hInt hlow
  · simpa [integral_const] using integral_mono_ae hInt (integrable_const (Real.log (t + R))) hhigh

/-- The logarithmic potential of a bounded real probability measure, minus `log t`, tends
to zero along the positive imaginary axis. -/
theorem tendsto_integral_log_norm_mul_I_sub_log_atTop (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : ∀ᵐ y ∂μ, |y| ≤ R) :
    Tendsto (fun t : ℝ ↦ (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂μ) -
      Real.log t) atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ ↦ Real.log (t + R) - Real.log t) atTop (𝓝 0) := by
    simpa using Real.tendsto_log_comp_add_sub_log R
  refine Filter.Tendsto.squeeze' tendsto_const_nhds hlog ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := (integral_log_norm_mul_I_bounds μ R hR t ht).1
    linarith
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := (integral_log_norm_mul_I_bounds μ R hR t ht).2
    linarith

/-- The logarithmic kernel integral under a positive affine pushforward of a real probability
measure, when the normalized kernel is integrable and nonzero almost everywhere. -/
theorem integral_log_norm_sub_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) {s : ℝ} (hs : 0 < s) (z : ℂ)
    (hne : ∀ᵐ y : ℝ ∂μ, (z - a) / s - y ≠ 0)
    (hint : Integrable (fun y : ℝ ↦ Real.log ‖(z - a) / s - y‖) μ) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂μ.map (fun y ↦ a + s * y)) =
      Real.log s + ∫ y : ℝ, Real.log ‖(z - a) / s - y‖ ∂μ := by
  let w : ℂ := (z - a) / s
  have hzw : (s : ℂ) * w = z - a := by
    dsimp [w]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hs.ne')
  have hkernel : (fun y : ℝ ↦ Real.log ‖z - (a + s * y)‖) =ᵐ[μ]
      fun y ↦ Real.log s + Real.log ‖w - y‖ := by
    filter_upwards [hne] with y hy
    have harg : z - (a + s * y) = (s : ℂ) * (w - y) := by
      rw [mul_sub, hzw]
      ring
    have hnorm : ‖z - (a + s * y)‖ = s * ‖w - y‖ := by
      rw [harg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm, Real.log_mul (ne_of_gt hs) (norm_ne_zero_iff.mpr hy)]
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  rw [integral_congr_ae hkernel, integral_add (integrable_const _) hint]
  simp

/-- The logarithmic potential of a Dirac mass is the translated logarithmic kernel. -/
@[simp]
theorem logarithmicPotential_dirac (w z : ℂ) :
    (dirac w).logarithmicPotential z = Real.log ‖z - w‖ := by
  simp [logarithmicPotential_def]

/-- The logarithmic potential with `log⁺ ‖w‖` subtracted from the kernel before integration.
This normalization controls contributions from poles escaping to infinity. -/
def normalizedLogarithmicPotential (μ : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ - Real.posLog ‖w‖ ∂μ

/-- The defining integral of the normalized logarithmic potential. -/
theorem normalizedLogarithmicPotential_def (μ : Measure ℂ) (z : ℂ) :
    μ.normalizedLogarithmicPotential z = ∫ w, Real.log ‖z - w‖ - Real.posLog ‖w‖ ∂μ := (rfl)

/-- The normalized potential of a Dirac mass is the kernel with its logarithmic offset. -/
@[simp]
theorem normalizedLogarithmicPotential_dirac (w z : ℂ) :
    (dirac w).normalizedLogarithmicPotential z = Real.log ‖z - w‖ - Real.posLog ‖w‖ := by
  simp [normalizedLogarithmicPotential_def]

/-- The logarithmic potential is a measurable function of the evaluation point. -/
@[fun_prop]
theorem measurable_logarithmicPotential (μ : Measure ℂ) [SFinite μ] :
    Measurable μ.logarithmicPotential := by
  unfold logarithmicPotential
  have h : Measurable (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖) := by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The normalized logarithmic potential is measurable in the evaluation point. -/
@[fun_prop]
theorem measurable_normalizedLogarithmicPotential (μ : Measure ℂ) [SFinite μ] :
    Measurable μ.normalizedLogarithmicPotential := by
  unfold normalizedLogarithmicPotential
  have h : Measurable (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖ - Real.posLog ‖p.2‖) :=
    by fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

private theorem exists_eLpNorm_normalizedLogKernel_le (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ w : ℂ,
      eLpNorm (fun z : ℂ ↦ Real.log ‖z - w‖ - Real.posLog ‖w‖) 2
        (volume.restrict (closedBall 0 R)) ≤ C := by
  let ν : Measure ℂ := volume.restrict (closedBall 0 R)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall 0 R).measure_lt_top.ne
  let c : ℝ := Real.posLog R + Real.log 2
  let g : ℂ → ℝ := fun z ↦ Real.posLog ‖z‖⁻¹
  let C := eLpNorm (fun _ : ℂ ↦ c) 2 ν
  have hg : MemLp g 2 volume := TauCeti.memLp_two_posLog_inv_norm
  refine ⟨C + eLpNorm g 2 volume,
    ENNReal.add_ne_top.2 ⟨(memLp_const c).eLpNorm_ne_top, hg.eLpNorm_ne_top⟩, fun w ↦ ?_⟩
  have heq := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    (by fun_prop : AEStronglyMeasurable g volume) (measurePreserving_sub_right volume w)
  have hbound : ∀ᵐ z ∂ν, ‖Real.log ‖z - w‖ - Real.posLog ‖w‖‖ ≤ ‖c + g (z - w)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall (μ := (volume : Measure ℂ))] with z hz
    have hz' : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz
    have hc : 0 ≤ c + g (z - w) := by
      dsimp [c, g]
      positivity [Real.posLog_nonneg (x := R), Real.posLog_nonneg (x := ‖z - w‖⁻¹)]
    rw [Real.norm_of_nonneg hc, Real.norm_eq_abs, ← Real.posLog_sub_posLog_inv (x := ‖z - w‖)]
    calc
      |Real.posLog ‖z - w‖ - Real.posLog ‖z - w‖⁻¹ - Real.posLog ‖w‖| =
          |(Real.posLog ‖z - w‖ - Real.posLog ‖w‖) - g (z - w)| := by
            congr 1
            dsimp [g]
            ring
      _ ≤ |Real.posLog ‖z - w‖ - Real.posLog ‖w‖| + g (z - w) := by
            simpa [g, abs_of_nonneg Real.posLog_nonneg] using
              abs_sub (Real.posLog ‖z - w‖ - Real.posLog ‖w‖) (Real.posLog ‖z - w‖⁻¹)
      _ ≤ c + g (z - w) := by
        have := Real.posLog_le_posLog (by linarith [norm_nonneg z]) hz'
        dsimp [c]
        have h₁ := Real.posLog_norm_add_le z (-w)
        have h₂ := Real.posLog_norm_add_le z (w - z)
        simp only [← sub_eq_add_neg, norm_neg] at h₁
        rw [add_comm z, sub_add_cancel, norm_sub_rev w z] at h₂
        have hdiff : |Real.posLog ‖z - w‖ - Real.posLog ‖w‖| ≤
            Real.posLog ‖z‖ + Real.log 2 := by
          rw [abs_le]
          constructor <;> linarith
        linarith
  have hm : Measurable (fun z : ℂ ↦ Real.log ‖z - w‖ - Real.posLog ‖w‖) := by fun_prop
  refine (eLpNorm_mono_ae hm.aestronglyMeasurable hbound).trans ?_
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  exact add_le_add_right ((eLpNorm_restrict_le _ _ _ _).trans_eq heq) C

private theorem integrable_normalizedLogKernel_prod (μ : Measure ℂ) [IsFiniteMeasure μ] (R : ℝ) :
    Integrable (fun p : ℂ × ℂ ↦ Real.log ‖p.1 - p.2‖ - Real.posLog ‖p.2‖)
      ((volume.restrict (closedBall 0 R)).prod μ) := by
  let ν : Measure ℂ := volume.restrict (closedBall 0 R)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall 0 R).measure_lt_top.ne
  let K : ℂ × ℂ → ℝ := fun p ↦ Real.log ‖p.1 - p.2‖ - Real.posLog ‖p.2‖
  have hK : Measurable K := by fun_prop
  obtain ⟨C, hC, hbound⟩ := exists_eLpNorm_normalizedLogKernel_le R
  have hLp (w : ℂ) : MemLp (fun z ↦ K (z, w)) 2 ν :=
    memLp_iff.mpr ((hbound w).trans_lt hC.lt_top)
  refine (integrable_prod_iff' hK.aestronglyMeasurable).2
    ⟨ae_of_all _ fun w ↦ (hLp w).integrable (by norm_num), ?_⟩
  have hfin : C * ν univ ^ (1 / 2 : ℝ) ≠ ∞ := by finiteness
  apply (integrable_const (C * ν univ ^ (1 / 2 : ℝ)).toReal).mono
    (hK.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
  filter_upwards with w
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
    Real.norm_of_nonneg ENNReal.toReal_nonneg]
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_toReal hfin, ofReal_integral_norm_eq_lintegral_eNorm
    ((hLp w).integrable (by norm_num)), ← eLpNorm_one_eq_lintegral_eNorm]
  · refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (by norm_num) (hLp w).aestronglyMeasurable).trans ?_
    norm_num
    exact mul_le_mul' (hbound w) le_rfl
  · exact (hLp w).aestronglyMeasurable

/-- For a finite measure, the normalized potential has a finite local `L²` bound that
depends only on the size of the observation window and the mass of the measure. -/
theorem exists_eLpNorm_normalizedLogarithmicPotential_le (R : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (μ : Measure ℂ) [IsFiniteMeasure μ],
      eLpNorm μ.normalizedLogarithmicPotential 2 (volume.restrict (closedBall 0 R)) ≤
        C * μ univ := by
  obtain ⟨C, hC, hbound⟩ := exists_eLpNorm_normalizedLogKernel_le R
  refine ⟨C, hC, fun μ _ ↦ ?_⟩
  let ν : Measure ℂ := volume.restrict (closedBall 0 R)
  let K : ℂ → ℂ → ℝ := fun z w ↦ Real.log ‖z - w‖ - Real.posLog ‖w‖
  have hK : Measurable (Function.uncurry K) := by
    simp only [K]
    fun_prop
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
    μ.measurable_normalizedLogarithmicPotential.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  calc
    _ ≤ (∫⁻ z, (∫⁻ w, ‖K z w‖ₑ ∂μ) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
      gcongr with z
      rw [normalizedLogarithmicPotential_def]
      exact eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ w, (∫⁻ z, ‖K z w‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ :=
      TauCeti.lintegral_Lp_lintegral_le hK.eNorm.aemeasurable (by norm_num)
    _ ≤ C * μ univ := by
      rw [← lintegral_const]
      apply lintegral_mono
      intro w
      have hm : Measurable (fun z ↦ K z w) :=
        hK.comp (measurable_id.prodMk measurable_const)
      simp only [K] at hm
      have h := hbound w
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
        hm.aestronglyMeasurable] at h
      simpa only [K, ENNReal.toReal_ofNat] using h

/-- The normalized potential of a finite measure is locally square integrable. -/
theorem memLp_normalizedLogarithmicPotential_closedBall (μ : Measure ℂ) [IsFiniteMeasure μ]
    (R : ℝ) : MemLp μ.normalizedLogarithmicPotential 2 (volume.restrict (closedBall 0 R)) := by
  obtain ⟨C, hC, hbound⟩ := exists_eLpNorm_normalizedLogarithmicPotential_le R
  exact memLp_iff.mpr ((hbound μ).trans_lt (by finiteness))

/-- The normalized logarithmic potential of a finite measure is locally integrable. -/
theorem locallyIntegrable_normalizedLogarithmicPotential (μ : Measure ℂ) [IsFiniteMeasure μ] :
    LocallyIntegrable μ.normalizedLogarithmicPotential := by
  rw [locallyIntegrable_iff]
  intro s hs
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : ℂ)
  have : IsFiniteMeasure ((volume : Measure ℂ).restrict (closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_lt_top.ne
  have hi : IntegrableOn μ.normalizedLogarithmicPotential (closedBall 0 R) :=
    (μ.memLp_normalizedLogarithmicPotential_closedBall R).integrable (by norm_num)
  exact hi.mono_set hR

/-- For almost every observation point, a finite logarithmic moment makes the
ordinary kernel integrable against the measure. -/
theorem ae_integrable_logarithmicKernel (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) μ) :
    ∀ᵐ z ∂volume, Integrable (fun w : ℂ ↦ Real.log ‖z - w‖) μ := by
  have h (n : ℕ) : ∀ᵐ z ∂(volume : Measure ℂ).restrict (closedBall 0 n),
      Integrable (fun w : ℂ ↦ Real.log ‖z - w‖) μ := by
    filter_upwards [(integrable_normalizedLogKernel_prod μ n).prod_right_ae] with z hz
    have he : ((fun w ↦ Real.log ‖z - w‖ - Real.posLog ‖w‖) +
        (fun w : ℂ ↦ Real.posLog ‖w‖)) = fun w ↦ Real.log ‖z - w‖ := by
      ext w
      simp
    rw [← he]
    exact hz.add hμ
  have hcover := (ae_restrict_iUnion_iff (μ := (volume : Measure ℂ))
    (fun n : ℕ ↦ closedBall 0 n) (fun z ↦ Integrable (fun w ↦ Real.log ‖z - w‖) μ)).2 h
  simpa only [iUnion_closedBall_nat, restrict_univ] using hcover

/-- The two potentials differ almost everywhere by the logarithmic moment. -/
theorem logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add
    (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) μ) :
    μ.logarithmicPotential =ᵐ[volume] fun z ↦ μ.normalizedLogarithmicPotential z +
      ∫ w, Real.posLog ‖w‖ ∂μ := by
  filter_upwards [μ.ae_integrable_logarithmicKernel hμ] with z hz
  rw [logarithmicPotential_def, normalizedLogarithmicPotential_def, integral_sub hz hμ,
    sub_add_cancel]

/-- With a finite logarithmic moment the ordinary potential is locally integrable. -/
theorem locallyIntegrable_logarithmicPotential (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) μ) :
    LocallyIntegrable μ.logarithmicPotential :=
  (μ.locallyIntegrable_normalizedLogarithmicPotential.add (locallyIntegrable_const _)).congr
    (μ.logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add hμ).symm

private theorem integral_laplacian_mul_normalizedLogKernel {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (w : ℂ) :
    ∫ z, Δ f z * (Real.log ‖z - w‖ - Real.posLog ‖w‖) =
      (2 * Real.pi) * f w := by
  have hlog (z : ℂ) :
      Real.log ‖z - w‖ = -(2 * Real.pi) * TauCeti.planarNewtonianKernel (z - w) := by
    rw [TauCeti.planarNewtonianKernel_def]
    field_simp
  have hi := hf.continuous_laplacian.integrable_of_hasCompactSupport (μ := volume) hc.laplacian
  have hJ := TauCeti.integrable_laplacian_mul_planarNewtonianKernel_sub hf hc w
  simp_rw [hlog, mul_sub, mul_left_comm _ (-(2 * Real.pi))]
  rw [integral_sub (hJ.const_mul _) (hi.mul_const _), integral_const_mul,
    TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub hf hc w,
    integral_mul_const, TauCeti.integral_laplacian_eq_zero_of_hasCompactSupport hf hc]
  ring

/-- The distributional Laplacian of the normalized potential of a finite measure is
`2π` times that measure, as tested against compactly supported `C²` functions. -/
theorem integral_laplacian_mul_normalizedLogarithmicPotential (μ : Measure ℂ)
    [IsFiniteMeasure μ] {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ z, Δ f z * μ.normalizedLogarithmicPotential z = (2 * Real.pi) * ∫ z, f z ∂μ := by
  obtain ⟨R, hR⟩ := hc.laplacian.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let ν : Measure ℂ := volume.restrict (closedBall 0 R)
  let J : ℂ × ℂ → ℝ := fun p ↦ Δ f p.1 * (Real.log ‖p.1 - p.2‖ - Real.posLog ‖p.2‖)
  have hzero : ∀ z ∉ closedBall (0 : ℂ) R, Δ f z = 0 :=
    fun z hz ↦ Function.notMem_support.mp (fun hz' ↦ hz (hR (subset_tsupport _ hz')))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuous_laplacian.continuousOn
  have hfactor : ∀ᵐ p ∂ν.prod μ, ‖Δ f p.1‖ ≤ C := by
    have h : ∀ᵐ z ∂ν, ‖Δ f z‖ ≤ C := (ae_restrict_mem measurableSet_closedBall).mono hC
    exact (quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae h
  have hJ : Integrable J (ν.prod μ) :=
    (integrable_normalizedLogKernel_prod μ R).bdd_mul
      ((hf.continuous_laplacian.measurable.comp measurable_fst).aestronglyMeasurable) hfactor
  calc
    _ = ∫ z, ∫ w, J (z, w) ∂μ ∂ν := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall 0 R)
        (fun z hz ↦ by simp [hzero z hz])]
      simp_rw [ν, J, integral_const_mul, normalizedLogarithmicPotential_def]
    _ = ∫ w, ∫ z, J (z, w) ∂ν ∂μ := (integral_prod J hJ).symm.trans (integral_prod_symm J hJ)
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with w
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ by simp [J, hzero z hz])]
      exact integral_laplacian_mul_normalizedLogKernel hf hc w

/-- The distributional Laplacian of the logarithmic potential of a finite measure with
finite logarithmic moment is `2π` times that measure. -/
theorem integral_laplacian_mul_logarithmicPotential (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) μ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ z, Δ f z * μ.logarithmicPotential z = (2 * Real.pi) * ∫ z, f z ∂μ := by
  have h := μ.logarithmicPotential_ae_eq_normalizedLogarithmicPotential_add hμ
  have hΔ := hf.continuous_laplacian.integrable_of_hasCompactSupport (μ := volume) hc.laplacian
  have hloc := μ.locallyIntegrable_normalizedLogarithmicPotential
  have hint := hloc.integrable_smul_right_of_hasCompactSupport
    hf.continuous_laplacian hc.laplacian
  rw [integral_congr_ae (h.mono fun z hz ↦ congrArg (Δ f z * ·) hz)]
  simp_rw [mul_add]
  rw [integral_add (by simpa only [smul_eq_mul, mul_comm] using hint) (hΔ.mul_const _),
    integral_mul_const, TauCeti.integral_laplacian_eq_zero_of_hasCompactSupport hf hc,
    zero_mul, add_zero]
  exact μ.integral_laplacian_mul_normalizedLogarithmicPotential hf hc

end

end MeasureTheory.Measure
