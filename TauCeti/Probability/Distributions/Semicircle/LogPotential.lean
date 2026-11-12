/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.Analysis.Complex.UpperHalfPlane.Log.Kernel
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

Let `m z = ∫ (y - z)⁻¹ dμ(y)` be the resolvent transform, which satisfies `m² + z m + 1 = 0` and
has positive imaginary part in the upper half-plane. The complex logarithmic potential
`H z = ∫ log (z - y) dμ(y)` has derivative `-m`, as does the primitive
`-z m / 2 - log (-m) - 1 / 2`; the two agree up to a constant, which vanishes at infinity. Taking
real parts gives the potential in the upper half-plane. The quadratic equation identifies the
boundary values of `m` on `(-2, 2)`, whose modulus is `1` and whose real part is `-x / 2`. The
potential is continuous up to the real axis by dominated convergence.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.6.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter
open scoped NNReal Topology

namespace TauCeti.Probability

private theorem ae_mem_Icc_semicircleReal_zero_one :
    ∀ᵐ y ∂semicircleReal 0 1, y ∈ Icc (-2 : ℝ) 2 := by
  simpa using ae_mem_Icc_semicircleReal 0 1

private theorem ae_ne_semicircleReal_zero_one (x : ℝ) :
    ∀ᵐ y ∂semicircleReal 0 1, y ≠ x := by
  let := nullSingletonClass_semicircleReal 0 one_pos
  exact (semicircleReal 0 1).ae_ne x

/-- The logarithmic kernel `y ↦ log |x - y|` is integrable against the semicircle law. -/
theorem integrable_log_abs_sub_semicircleReal (x a : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ ↦ Real.log |x - y|) (semicircleReal a v) := by
  rcases eq_zero_or_pos v with rfl | hv
  · rw [semicircleReal_zero_var]
    exact integrable_dirac (by simp)
  · let l := a - 2 * Real.sqrt v
    let u := a + 2 * Real.sqrt v
    have hlu : l ≤ u := by dsimp [l, u]; linarith [Real.sqrt_nonneg (v : ℝ)]
    have hlog : IntervalIntegrable (fun y : ℝ ↦ Real.log (x - y)) volume l u := by
      have h := (intervalIntegral.intervalIntegrable_log' (a := x - l) (b := x - u)).comp_sub_left x
      simpa using h
    have hint : IntegrableOn (fun y : ℝ ↦ Real.log |x - y|) (Icc l u) volume := by
      simp only [Real.log_abs]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hlu).1 hlog
    have h1 : Integrable (fun y : ℝ ↦ Real.log |x - y|)
        (ENNReal.ofReal (Real.pi * Real.sqrt v)⁻¹ • volume.restrict (Icc l u)) :=
      hint.smul_measure ENNReal.ofReal_ne_top
    have hrestr : (semicircleReal a v).restrict (Icc l u) = semicircleReal a v :=
      restrict_Icc_semicircleReal a v
    rw [← hrestr]
    refine h1.mono_measure ?_
    rw [← Measure.restrict_smul]
    exact Measure.restrict_mono_measure (semicircleReal_le_smul_volume a hv) _

private theorem tendsto_log_norm_sub_integral (x : ℝ) :
    Tendsto
      (fun ε : ℝ ↦ ∫ y : ℝ,
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1)
      (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1)) := by
  let bound : ℝ → ℝ := fun y ↦ ‖Real.log |x - y|‖ + Real.log (|x| + 3)
  have hbound_integrable : Integrable bound (semicircleReal 0 1) := by
    have hlog := (integrable_log_abs_sub_semicircleReal x 0 1).norm
    have hconst := integrable_const (Real.log (|x| + 3)) (μ := semicircleReal 0 1)
    simpa [bound, Real.norm_eq_abs] using hlog.add hconst
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
    filter_upwards [ae_mem_Icc_semicircleReal_zero_one,
      ae_ne_semicircleReal_zero_one x] with y hy hxy
    have hy' : |y| ≤ 2 := abs_le.mpr ⟨hy.1, hy.2⟩
    simpa only [bound, show (|x| + 2 + 1 : ℝ) = |x| + 3 by ring] using
      TauCeti.log_norm_sub_bound x y ε 2 hεpos hεle hy' hxy
  · filter_upwards [ae_ne_semicircleReal_zero_one x] with y hxy
    have harg : ContinuousAt
        (fun ε : ℝ ↦ (x : ℂ) + (ε : ℂ) * Complex.I - y) 0 := by
      fun_prop
    have hnorm : ‖(x : ℂ) - y‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      rw [← Complex.ofReal_sub]
      exact_mod_cast (sub_ne_zero.mpr (Ne.symm hxy))
    have hnormeq : ‖(x : ℂ) - y‖ = |x - y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hEnd :
        Real.log ‖(x : ℂ) + (0 : ℂ) * Complex.I - y‖ = Real.log |x - y| := by
      have hzero : (x : ℂ) + (0 : ℂ) * Complex.I - y = (x : ℂ) - y := by simp
      rw [hzero, hnormeq]
    have hlog := (harg.norm.log (by simpa using hnorm)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    rw [← hEnd]
    exact hlog

/-- The Stieltjes transform of the standard semicircle law. -/
private def m (z : ℂ) : ℂ := resolventTransform (semicircleReal 0 1) z

private def primitive (z : ℂ) : ℂ :=
  -(z * m z) / 2 - Complex.log (-(m z)) - 1 / 2

section UpperHalfPlane

variable {z : ℂ}

private theorem integrable_log_sub {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun y : ℝ ↦ Complex.log (w - y)) (semicircleReal 0 1) := by
  have h : IntegrableOn (fun y : ℝ ↦ Complex.log (w - y)) (Icc (-2) 2) (semicircleReal 0 1) :=
    (continuous_log_sub hw).continuousOn.integrableOn_compact isCompact_Icc
  have hrestrict : (semicircleReal 0 1).restrict (Icc (-2) 2) = semicircleReal 0 1 := by
    simpa using restrict_Icc_semicircleReal 0 1
  rwa [IntegrableOn, hrestrict] at h

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
  exact not_mem_range_ofReal_of_im_pos hz ⟨x, hx⟩

private theorem m_quad (hz : 0 < z.im) : m z * m z + z * m z + 1 = 0 := by
  have h := resolventTransform_semicircleReal_quadratic_eq_zero (a := 0) (v := 1) (z := z) (by
    rintro ⟨x, -, hx⟩
    exact not_mem_range_ofReal_of_im_pos hz ⟨x, hx⟩)
  simpa [m] using h

private theorem m_im_pos (hz : 0 < z.im) : 0 < (m z).im :=
  im_resolventTransform_pos (μ := semicircleReal 0 1) (IsProbabilityMeasure.ne_zero _) hz

private theorem integral_log_norm_sub (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) =
      (∫ y : ℝ, Complex.log (z - y) ∂semicircleReal 0 1).re := by
  calc
    ∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1 =
        ∫ y : ℝ, (Complex.log (z - y)).re ∂semicircleReal 0 1 := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Complex.log_re]
    _ = (∫ y : ℝ, Complex.log (z - y) ∂semicircleReal 0 1).re :=
      integral_re (integrable_log_sub hz)

private theorem hasDerivAt_logPotential_eq_neg_m (hz : 0 < z.im) :
    HasDerivAt
      (fun w : ℂ ↦ ∫ y : ℝ, Complex.log (w - y) ∂semicircleReal 0 1)
      (-m z) z := by
  convert hasDerivAt_logPotential hz using 1
  rw [m, MeasureTheory.resolventTransform_apply]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  simp only [resolvent, Ring.inverse_eq_inv]
  have hyz : (algebraMap ℝ ℂ) y - z ≠ 0 :=
    sub_ne_zero.mpr (by
      intro hy
      exact not_mem_range_ofReal_of_im_pos hz ⟨y, hy⟩)
  have hzy : z - (y : ℂ) ≠ 0 := by
    intro h
    apply hyz
    rw [sub_eq_zero] at h ⊢
    exact h.symm
  field_simp [hyz, hzy]
  rw [RCLike.algebraMap_eq_ofReal]
  exact neg_sub _ _

private theorem mem_slitPlane_neg_m (hz : 0 < z.im) : -(m z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have hm := (m_im_pos hz).ne'
  simpa using neg_ne_zero.mpr hm

private theorem m_ne_zero (hz : 0 < z.im) : m z ≠ 0 := by
  intro hm
  have h := m_quad hz
  rw [hm] at h
  norm_num at h

private theorem deriv_m_quad (hz : 0 < z.im) {d : ℂ} (hdm : HasDerivAt m d z) :
    d * m z + m z * d + m z + z * d = 0 := by
  have hq : HasDerivAt (fun w : ℂ ↦ m w * m w + w * m w + 1)
      (d * m z + m z * d + m z + z * d) z := by
    convert ((hdm.mul hdm).add ((hasDerivAt_id z).mul hdm)).add
      (hasDerivAt_const z 1) using 1
    · funext w
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    · simp only [id_eq]
      ring
  have hEq : (fun w : ℂ ↦ m w * m w + w * m w + 1) =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [Metric.ball_mem_nhds z (by positivity : 0 < z.im / 2)] with w hw
    simpa using m_quad (by
      have h := im_gt_of_mem_ball hw
      linarith)
  have hzero := (hasDerivAt_const z 0).congr_of_eventuallyEq hEq
  have := hzero.deriv
  rw [hq.deriv] at this
  exact this

private theorem hasDerivAt_primitive (hz : 0 < z.im) :
    HasDerivAt primitive (-m z) z := by
  obtain ⟨d, hdm⟩ := hasDerivAt_m hz
  have hq0 := deriv_m_quad hz hdm
  have hm0 := m_ne_zero hz
  have hlog := HasDerivAt.clog (hdm.neg) (mem_slitPlane_neg_m hz)
  have hprod := (hasDerivAt_id z).mul hdm
  have hprim :
      HasDerivAt (fun w : ℂ ↦ -(w * m w) / 2 - Complex.log (-(m w)) - 1 / 2)
        (-(m z + z * d) / 2 - (-d) / (-(m z))) z := by
    convert (((hprod.const_mul (-1 / 2)).sub hlog).sub
      (hasDerivAt_const z (1 / 2))) using 1
    · funext w
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      simp only [Pi.neg_apply, div_eq_mul_inv]
      ring
    · simp only [id]
      field_simp [hm0]
      simp only [Pi.neg_apply]
      ring
  have hval : -(m z + z * d) / 2 - (-d) / (-(m z)) = -m z := by
    have hq1 := m_quad hz
    field_simp [hm0]
    linear_combination m z * hq0 - 2 * d * hq1
  convert hprim using 1
  · rfl
  · exact hval.symm

private theorem logPotential_sub_primitive_is_const {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ y : ℝ, Complex.log (z - y) ∂semicircleReal 0 1) - primitive z =
      (∫ y : ℝ, Complex.log (w - y) ∂semicircleReal 0 1) - primitive w := by
  let D : ℂ → ℂ :=
    fun u ↦ (∫ y : ℝ, Complex.log (u - y) ∂semicircleReal 0 1) - primitive u
  have hD (u : ℂ) (hu : 0 < u.im) : HasDerivAt D 0 u := by
    convert (hasDerivAt_logPotential_eq_neg_m hu).sub (hasDerivAt_primitive hu) using 1; simp
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_lt continuous_const Complex.continuous_im
  have hconv : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hdiff : DifferentiableOn ℂ D {u : ℂ | 0 < u.im} :=
    fun u hu ↦ (hD u hu).differentiableAt.differentiableWithinAt
  have hderiv : {u : ℂ | 0 < u.im}.EqOn (deriv D) 0 := by
    intro u hu
    exact (hD u hu).deriv
  have h := hopen.is_const_of_deriv_eq_zero hconv hdiff hderiv hz hw
  exact h

private theorem primitive_re (z : ℂ) :
    (primitive z).re = (-(z * m z) / 2).re - Real.log ‖m z‖ - 1 / 2 := by
  simp [primitive, Complex.log_re, norm_neg]

private theorem real_logPotential_sub_primitive_is_const {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) - (primitive z).re =
      (∫ y : ℝ, Real.log ‖w - y‖ ∂semicircleReal 0 1) - (primitive w).re := by
  have h := congrArg Complex.re (logPotential_sub_primitive_is_const hz hw)
  simpa only [Complex.sub_re, integral_log_norm_sub hz, integral_log_norm_sub hw] using h

private theorem integrable_log_norm_imaginary (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ ↦ Real.log ‖(t : ℂ) * Complex.I - y‖)
      (semicircleReal 0 1) := by
  have hz : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
  have h := (integrable_log_sub hz).re
  refine h.congr ?_
  filter_upwards with y
  exact Complex.log_re _

private theorem log_norm_imaginary_bounds (t : ℝ) (ht : 0 < t) :
    Real.log t ≤ ∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1 ∧
      (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) ≤
        Real.log (t + 2) := by
  have hInt := integrable_log_norm_imaginary t ht
  have hlow : ∀ᵐ (y : ℝ) ∂(semicircleReal (0 : ℝ) (1 : ℝ≥0)),
      Real.log t ≤ Real.log ‖(t : ℂ) * Complex.I - y‖ := by
    filter_upwards with y
    apply Real.log_le_log (by linarith)
    have h := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - (y : ℂ))
    have him : (((t : ℂ) * Complex.I - y).im) = t := by simp
    rw [him] at h
    simpa [abs_of_pos ht] using h
  have hhigh : ∀ᵐ (y : ℝ) ∂(semicircleReal (0 : ℝ) (1 : ℝ≥0)),
      Real.log ‖(t : ℂ) * Complex.I - y‖ ≤ Real.log (t + 2) := by
    filter_upwards [ae_mem_Icc_semicircleReal_zero_one] with y hy
    have him : (((t : ℂ) * Complex.I - (y : ℂ)).im) = t := by simp
    have hnorm := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - (y : ℂ))
    rw [him] at hnorm
    have hnormpos : 0 < ‖(t : ℂ) * Complex.I - y‖ :=
      lt_of_lt_of_le ht (by simpa [abs_of_pos ht] using hnorm)
    apply Real.log_le_log hnormpos
    · calc
        ‖(t : ℂ) * Complex.I - (y : ℂ)‖ ≤
          ‖(t : ℂ) * Complex.I‖ + ‖(y : ℂ)‖ :=
          norm_sub_le _ _
        _ = t + |y| := by simp [abs_of_pos ht]
        _ ≤ t + 2 := by
          have hyabs : |y| ≤ 2 := abs_le.mpr hy
          linarith
  constructor
  · simpa [integral_const] using integral_mono_ae (integrable_const (Real.log t)) hInt hlow
  · simpa [integral_const] using integral_mono_ae hInt (integrable_const (Real.log (t + 2))) hhigh

private theorem tendsto_log_norm_imaginary_sub_log_atTop :
    Tendsto
      (fun t : ℝ ↦ (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
        Real.log t) atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ ↦ Real.log (t + 2) - Real.log t) atTop (𝓝 0) := by
    simpa using Real.tendsto_log_comp_add_sub_log 2
  refine Filter.Tendsto.squeeze' tendsto_const_nhds hlog ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := (log_norm_imaginary_bounds t ht).1
    linarith
  · filter_upwards [eventually_gt_atTop 0] with t ht
    have h := (log_norm_imaginary_bounds t ht).2
    linarith

private theorem tendsto_primitive_re_sub_log_atTop :
    Tendsto (fun t : ℝ ↦ (primitive ((t : ℂ) * Complex.I)).re - Real.log t)
      atTop (𝓝 0) := by
  have hcont : ContinuousAt (fun u : ℝ ↦ u / 2 - Real.log u - 1 / 2) 1 := by
    fun_prop (disch := norm_num)
  have h := hcont.tendsto.comp tendsto_mul_semicircleResolvent_im_atTop
  have heq : ∀ᶠ t : ℝ in atTop,
      (primitive ((t : ℂ) * Complex.I)).re - Real.log t =
        (t * (m (t * Complex.I)).im) / 2 -
          Real.log (t * (m (t * Complex.I)).im) - 1 / 2 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hzt : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
    have hb := m_im_pos hzt
    have hm : (m ((t : ℂ) * Complex.I)).re = 0 := by
      simpa [m, semicircleResolvent] using (semicircleResolvent_at_imaginary_axis t ht).1
    have hmval : m ((t : ℂ) * Complex.I) =
        (m ((t : ℂ) * Complex.I)).im * Complex.I := by
      apply Complex.ext <;> simp [hm]
    have hnorm : ‖m ((t : ℂ) * Complex.I)‖ =
        (m ((t : ℂ) * Complex.I)).im := by
      rw [hmval]
      simp [abs_of_pos hb]
    have hfirst :
        (-( ((t : ℂ) * Complex.I) * m ((t : ℂ) * Complex.I)) / 2).re =
          t * (m ((t : ℂ) * Complex.I)).im / 2 := by
      rw [hmval]
      simp
    rw [primitive_re, hfirst, hnorm]
    rw [Real.log_mul (ne_of_gt ht) (ne_of_gt hb)]
    ring
  have h' := Filter.Tendsto.congr' (EventuallyEq.symm heq) h
  simpa using h'

private theorem real_logPotential_eq_primitive_re {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) = (primitive z).re := by
  let C := (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) - (primitive z).re
  have hG : Tendsto
      (fun t : ℝ ↦
        (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
          (primitive ((t : ℂ) * Complex.I)).re) atTop (𝓝 0) := by
    have hH := tendsto_log_norm_imaginary_sub_log_atTop
    have hF := tendsto_primitive_re_sub_log_atTop
    have h := hH.sub hF
    have hfun :
        (fun t : ℝ ↦
          (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
            (primitive ((t : ℂ) * Complex.I)).re) =
          (fun (t : ℝ) ↦
            ((∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
              Real.log t) -
              ((primitive ((t : ℂ) * Complex.I)).re - Real.log t)) := by
      funext t
      ring
    rw [hfun]
    simpa using h
  have hEq : (fun _ : ℝ ↦ C) =ᶠ[atTop] fun t ↦
      (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
        (primitive ((t : ℂ) * Complex.I)).re := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hzt : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
    exact real_logPotential_sub_primitive_is_const hz hzt
  have hconst : Tendsto (fun _ : ℝ ↦ C) atTop (𝓝 0) := hG.congr' hEq.symm
  have hzero := tendsto_nhds_unique tendsto_const_nhds hconst
  dsimp [C] at hzero
  linarith

private theorem log_norm_eq_primitive_re {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) =
      (-(z * m z) / 2).re - Real.log ‖m z‖ - 1 / 2 := by
  rw [real_logPotential_eq_primitive_re hz, primitive_re]

end UpperHalfPlane

private theorem tendsto_log_norm_m_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto (fun ε : ℝ ↦ Real.log ‖semicircleResolventBoundary x ε‖) (𝓝[>] 0) (𝓝 0) := by
  let Q : ℝ → ℝ := fun ε ↦ semicircleResolventBoundaryNormSq x ε
  have hQ : Tendsto Q (𝓝[>] 0) (𝓝 1) := tendsto_semicircleResolventBoundaryNormSq hx
  have hlogQ : Tendsto (Real.log ∘ Q) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log (by norm_num)
    simpa only [Real.log_one] using hcont.tendsto.comp hQ
  have hEq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Real.log ‖semicircleResolventBoundary x ε‖ =
        Real.log (Q ε) / 2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let q : ℝ := semicircleResolventBoundaryNormSq x ε
    have hqnorm : q = ‖semicircleResolventBoundary x ε‖ ^ 2 := by
      dsimp [q, semicircleResolventBoundaryNormSq]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hnorm : ‖semicircleResolventBoundary x ε‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (m_ne_zero (by simpa [semicircleResolventBoundary] using hε))
    have hlog : Real.log q = 2 * Real.log ‖semicircleResolventBoundary x ε‖ := by
      rw [hqnorm, pow_two, Real.log_mul hnorm hnorm]
      ring
    have hlognorm : Real.log ‖semicircleResolventBoundary x ε‖ = Real.log q / 2 := by linarith
    simpa [Q, q, semicircleResolventBoundary] using hlognorm
  have hhalf : Tendsto (fun ε ↦ Real.log (Q ε) / 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlogQ.div_const 2
  exact Filter.Tendsto.congr' (EventuallyEq.symm hEq) hhalf

private theorem tendsto_primitive_re_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦
        (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4 - 1 / 2)) := by
  let A : ℝ → ℝ := fun ε ↦ (semicircleResolventBoundary x ε).re
  let B : ℝ → ℝ := fun ε ↦ ε * (semicircleResolventBoundary x ε).im
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (-x / 2)) := tendsto_semicircleResolventBoundary_re hx
  have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := tendsto_eps_mul_semicircleResolventBoundary_im hx
  have hlog : Tendsto
      (fun ε : ℝ ↦ Real.log ‖semicircleResolventBoundary x ε‖) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_norm_m_boundary hx
  have hxa : Tendsto (fun ε ↦ x * A ε) (𝓝[>] 0) (𝓝 (x * (-x / 2))) := by
    simpa [A] using tendsto_const_nhds.mul hA
  have hterm₁ : Tendsto (fun ε ↦ -(x * A ε) / 2) (𝓝[>] 0) (𝓝 (x ^ 2 / 4)) := by
    have h := hxa.const_mul (-1 / 2)
    have hfun : (fun ε : ℝ ↦ -(x * A ε) / 2) =ᶠ[𝓝[>] 0]
        fun ε ↦ -1 / 2 * (x * A ε) := by
      filter_upwards with ε
      ring
    have h' := Filter.Tendsto.congr' (EventuallyEq.symm hfun) h
    have hlim : -1 / 2 * (x * (-x / 2)) = x ^ 2 / 4 := by ring
    rw [← hlim]
    exact h'
  have hterm₂ : Tendsto (fun ε ↦ B ε / 2) (𝓝[>] 0) (𝓝 0) := by
    have h := hB.div_const 2
    simpa using h
  have hsum : Tendsto
      (fun ε ↦ (-(x * A ε) / 2 + B ε / 2) - Real.log ‖semicircleResolventBoundary x ε‖)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4)) := by
    have h := (hterm₁.add hterm₂).sub hlog
    simpa using h
  have hfinal := hsum.add (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ (-1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 (-1 / 2)))
  have hEq : (fun ε : ℝ ↦ (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re) =ᶠ[𝓝[>] 0]
      fun ε ↦
        (-(x * A ε) / 2 + B ε / 2) -
          Real.log ‖semicircleResolventBoundary x ε‖ + (-1 / 2) := by
    filter_upwards with ε
    let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
    let a : ℝ := (semicircleResolventBoundary x ε).re
    let b : ℝ := (semicircleResolventBoundary x ε).im
    have hfirst :
        (-(z * semicircleResolventBoundary x ε) / 2).re = -(x * a) / 2 + ε * b / 2 := by
      simp [z, a, b, semicircleResolventBoundary, Complex.mul_re]
      ring
    have hprimitive :
        (primitive z).re =
          (-(z * semicircleResolventBoundary x ε) / 2).re -
            Real.log ‖semicircleResolventBoundary x ε‖ - 1 / 2 := by
      rw [primitive_re]
      simp [z, semicircleResolventBoundary, semicircleResolvent, m]
    rw [hprimitive, hfirst]
    ring
  have h' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hfinal
  have hlimit : x ^ 2 / 4 + (-1 / 2) = x ^ 2 / 4 - 1 / 2 := by ring
  rw [← hlimit]
  exact h'

/-- The logarithmic potential of the standard semicircle law on its support. -/
theorem integral_log_abs_sub_semicircleReal (x : ℝ) (hx : x ∈ Icc (-2) 2) :
    (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1) = x ^ 2 / 4 - 1 / 2 := by
  let H : ℝ → ℝ := fun ε ↦
    ∫ y : ℝ, Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1
  have hH : Tendsto H (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1)) := by
    simpa [H] using tendsto_log_norm_sub_integral x
  have hEq : H =ᶠ[𝓝[>] 0] fun ε ↦
      (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
    simp only [Set.mem_Ioi] at hε
    have hz : 0 < z.im := by simp [z, hε]
    calc
      H ε = ∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1 := by
        simp [H, z]
      _ = (-(z * m z) / 2).re - Real.log ‖m z‖ - 1 / 2 :=
        log_norm_eq_primitive_re hz
      _ = (primitive z).re := (primitive_re z).symm
  have hprimitive := tendsto_primitive_re_boundary hx
  have hH' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hprimitive
  exact tendsto_nhds_unique hH hH'

end TauCeti.Probability
