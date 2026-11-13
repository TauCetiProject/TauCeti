/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.Analysis.Complex.UpperHalfPlane.Log.Kernel
import TauCeti.Analysis.Complex.UpperHalfPlane.Cpow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Basic.Complex.OfRealSub

/-!
# The logarithmic potential of the semicircle law

For a positive-variance semicircle law `semicircleReal a v`, the logarithmic potential on its
support is `(x - a) ^ 2 / (4 * v) + log (√v) - 1 / 2`. The standard law `semicircleReal 0 1`
therefore has potential `x ^ 2 / 4 - 1 / 2` on `[-2, 2]`. Hence the effective potential
`x ^ 2 / 2 - 2 ∫ log |x - y| dμ(y)` of the Gaussian beta gas is constant on the support, which is
the Euler–Lagrange equation characterizing the semicircle law as the equilibrium measure.

## Main results

* `TauCeti.Probability.integrable_log_abs_sub_semicircleReal`: the logarithmic kernel is
  integrable against the semicircle law.
* `TauCeti.Probability.integral_log_abs_sub_semicircleReal`: the logarithmic potential on the
  support of any positive-variance semicircle law.

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

/-- The logarithmic kernel converges in integral to its real-axis value for a positive-variance
semicircle law. -/
theorem tendsto_integral_log_norm_sub_semicircleReal (a x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Tendsto
      (fun ε : ℝ ↦ ∫ y : ℝ,
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal a v)
      (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v)) := by
  let R : ℝ := |a| + 2 * Real.sqrt v
  let bound : ℝ → ℝ := fun y ↦ ‖Real.log |x - y|‖ + Real.log (|x| + R + 1)
  have hR : 0 ≤ R := by positivity
  have hbound_integrable : Integrable bound (semicircleReal a v) := by
    have hlog := (integrable_log_abs_sub_semicircleReal x a v).norm
    have hconst := integrable_const (Real.log (|x| + R + 1)) (μ := semicircleReal a v)
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
    filter_upwards [ae_mem_Icc_semicircleReal a v,
      (by
        let _ := nullSingletonClass_semicircleReal a hv
        exact (semicircleReal a v).ae_ne x)] with y hy hxy
    have hy' : |y| ≤ R := by
      have hya : |y - a| ≤ 2 * Real.sqrt v := by
        apply abs_le.mpr
        constructor <;> dsimp [R] at * <;> linarith [hy.1, hy.2]
      apply abs_le.mpr
      constructor
      · have hyLower := (abs_le.mp hya).1
        dsimp [R]
        linarith [neg_abs_le a]
      · have hyUpper := (abs_le.mp hya).2
        dsimp [R]
        linarith [le_abs_self a]
    simpa [bound] using
      norm_log_norm_add_mul_I_sub_le x y ε R (by rw [abs_of_pos hεpos]; exact hεle)
        hy' hxy
  · filter_upwards [(by
    let _ := nullSingletonClass_semicircleReal a hv
    exact (semicircleReal a v).ae_ne x)] with y hxy
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
    (continuous_log_sub_of_im_pos hw).continuousOn.integrableOn_compact isCompact_Icc
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
    (Filter.Eventually.of_forall fun y w hw ↦ Complex.norm_sub_inv_le_of_mem_ball hw y)
    (integrable_const _)
    (Filter.Eventually.of_forall fun y w hw ↦ by
      have hw' : 0 < w.im := by have := im_gt_of_mem_ball hw; linarith
      have hd : HasDerivAt (fun w : ℂ ↦ w - (y : ℂ)) 1 w := (hasDerivAt_id w).sub_const (y : ℂ)
      simpa using HasDerivAt.clog hd (sub_ofReal_mem_slitPlane_of_im_pos hw' y))
  exact key.2

private theorem hasDerivAt_m (hz : 0 < z.im) : ∃ d, HasDerivAt m d z := by
  refine ⟨_, hasDerivAt_resolventTransform (μ := semicircleReal 0 1) z ?_⟩
  rintro ⟨x, -, hx⟩
  exact hz.ne' (by rw [← hx]; simp)

private theorem m_quad (hz : 0 < z.im) : m z * m z + z * m z + 1 = 0 := by
  have h := resolventTransform_semicircleReal_quadratic_eq_zero (a := 0) (v := 1) (z := z) (by
    exact Complex.notMem_image_ofReal_of_im_ne_zero hz.ne')
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
      have him : z.im = 0 := by
        simpa using (congrArg Complex.im hy).symm
      exact hz.ne' him)
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
    filter_upwards [ae_mem_Icc_semicircleReal 0 1] with y hy
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
          have hy' : y ∈ Icc (-2) 2 := by simpa using hy
          have hyabs : |y| ≤ 2 := abs_le.mpr hy'
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
  have hcomplex : Tendsto
      (fun t : ℝ ↦ t * Complex.I * m (t * Complex.I)) atTop (𝓝 (-1 : ℂ)) := by
    simpa [m] using
      (MeasureTheory.tendsto_mul_I_mul_resolventTransform
        (μ := semicircleReal 0 1))
  have hreal := Complex.continuous_re.neg.continuousAt.tendsto.comp hcomplex
  have hreal' : Tendsto
      (fun t : ℝ ↦ -(t * Complex.I * m (t * Complex.I)).re) atTop (𝓝 (1 : ℝ)) := by
    change Tendsto (fun t : ℝ ↦ -(t * Complex.I * m (t * Complex.I)).re)
      atTop (𝓝 (-( (-1 : ℂ).re))) at hreal
    simpa using hreal
  have hEqIm : (fun t : ℝ ↦ t * (m (t * Complex.I)).im) =ᶠ[atTop]
      fun t ↦ -(t * Complex.I * m (t * Complex.I)).re := by
    filter_upwards with t
    simp [Complex.mul_re]
  have hIm := Filter.Tendsto.congr' (EventuallyEq.symm hEqIm) hreal'
  have h := hcont.tendsto.comp hIm
  have heq : ∀ᶠ t : ℝ in atTop,
      (primitive ((t : ℂ) * Complex.I)).re - Real.log t =
        (t * (m (t * Complex.I)).im) / 2 -
          Real.log (t * (m (t * Complex.I)).im) - 1 / 2 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hzt : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
    have hb := m_im_pos hzt
    have hm : (m ((t : ℂ) * Complex.I)).re = 0 := by
      simpa [m] using
        (re_eq_zero_and_sq_im_add_mul_eq_one_resolventTransform_semicircleReal_mul_I
          0 t 1 ht).1
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

/-- In the upper half-plane, the logarithmic potential of a positive-variance semicircle law is
expressed by its resolvent transform. -/
theorem integral_log_norm_sub_semicircleReal (a : ℝ) {v : ℝ≥0} (hv : 0 < v) {z : ℂ}
    (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
      ( -((z - a) * resolventTransform (semicircleReal a v) z) / 2).re -
        Real.log ‖resolventTransform (semicircleReal a v) z‖ - 1 / 2 := by
  let s : ℝ := Real.sqrt v
  let w : ℂ := (z - a) / s
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hw : 0 < w.im := by
    have hwm : w.im = z.im / s := by
      dsimp [w]
      rw [div_im]
      simp [Complex.normSq_apply]
      field_simp [ne_of_gt hs]
    rw [hwm]
    exact div_pos hz hs
  have hs2 : s ^ 2 = v := by
    dsimp [s]
    exact Real.sq_sqrt v.coe_nonneg
  have hvar : Real.toNNReal (s ^ 2) * (1 : ℝ≥0) = v := by
    apply NNReal.coe_injective
    simp [hs2]
  have hmap : (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
      semicircleReal a v := by
    calc
      (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
          semicircleReal (a + s * 0) (Real.toNNReal (s ^ 2) * 1) :=
        map_affine_semicircleReal 0 a s 1
      _ = semicircleReal a v := by simp [hvar]
  have hmapInt :
      (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
        ∫ y : ℝ, Real.log ‖z - (a + s * y)‖ ∂semicircleReal 0 1 := by
    rw [← hmap]
    rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
  have hlogInt :
      Integrable (fun y : ℝ ↦ Real.log ‖w - y‖) (semicircleReal 0 1) := by
    refine (integrable_log_sub hw).re.congr ?_
    filter_upwards with y
    simpa using Complex.log_re (w - (y : ℂ))
  have hkernel : (fun y : ℝ ↦ Real.log ‖z - (a + s * y)‖) =ᵐ[semicircleReal 0 1]
      fun y ↦ Real.log s + Real.log ‖w - y‖ := by
    filter_upwards with y
    have harg : z - (a + s * y) = (s : ℂ) * (w - y) := by
      dsimp [w]
      field_simp [ne_of_gt hs]
      ring
    have hnorm : ‖z - (a + s * y)‖ = s * ‖w - y‖ := by
      rw [harg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hwy : w - (y : ℂ) ≠ 0 := by
      intro h
      have h' : w = (y : ℂ) := sub_eq_zero.mp h
      have him : w.im = 0 := by rw [h']; simp
      exact hw.ne' him
    rw [hnorm, Real.log_mul (ne_of_gt hs) (norm_ne_zero_iff.mpr hwy)]
  have hstd := log_norm_eq_primitive_re hw
  have hRT : resolventTransform (semicircleReal a v) z =
      (s : ℂ)⁻¹ * resolventTransform (semicircleReal 0 1) w := by
    rw [← hmap]
    simpa [w] using resolventTransform_map_affine a s (ne_of_gt hs) z
  have harg : z - a = (s : ℂ) * w := by
    dsimp [w]
    field_simp [ne_of_gt hs]
  have hprod :
      (z - a) * ((s : ℂ)⁻¹ * m w) = w * m w := by
    rw [harg]
    field_simp [ne_of_gt hs]
  have hnorm :
      ‖(s : ℂ)⁻¹ * m w‖ = s⁻¹ * ‖m w‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hlog :
      Real.log ‖(s : ℂ)⁻¹ * m w‖ = Real.log ‖m w‖ - Real.log s := by
    rw [hnorm, Real.log_mul (inv_ne_zero (ne_of_gt hs)) (norm_ne_zero_iff.mpr (m_ne_zero hw)),
      Real.log_inv]
    ring
  have hprod' :
      (z - a) * ((s : ℂ)⁻¹ * resolventTransform (semicircleReal 0 1) w) =
        w * resolventTransform (semicircleReal 0 1) w := by
    simpa [m] using hprod
  have hlog' :
      Real.log ‖(s : ℂ)⁻¹ * resolventTransform (semicircleReal 0 1) w‖ =
        Real.log ‖resolventTransform (semicircleReal 0 1) w‖ - Real.log s := by
    simpa [m] using hlog
  calc
    ∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v =
        Real.log s + ∫ y : ℝ, Real.log ‖w - y‖ ∂semicircleReal 0 1 := by
          rw [hmapInt, integral_congr_ae hkernel, integral_add (integrable_const _) hlogInt]
          simp
    _ = Real.log s + (-(w * m w) / 2).re - Real.log ‖m w‖ - 1 / 2 := by
      rw [hstd]
      ring
    _ = ( -((z - a) * resolventTransform (semicircleReal a v) z) / 2).re -
        Real.log ‖resolventTransform (semicircleReal a v) z‖ - 1 / 2 := by
      rw [hRT, hprod', hlog']
      simp only [m]
      ring_nf

private theorem tendsto_log_norm_m_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦ Real.log ‖resolventTransform (semicircleReal 0 1)
        ((x : ℂ) + (ε : ℂ) * Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  let c : ℂ := ((-x / 2 : ℝ) : ℂ) + (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I
  have hrad : 0 ≤ 1 - x ^ 2 / 4 := by
    have hleft : 0 ≤ x + 2 := by linarith [hx.1]
    have hright : 0 ≤ 2 - x := by linarith [hx.2]
    nlinarith [mul_nonneg hleft hright]
  have hcSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_apply]
    simp [c]
    nlinarith [Real.sq_sqrt hrad]
  have hcNorm : ‖c‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hcSq] at h
    nlinarith [norm_nonneg c]
  have hM := tendsto_resolventTransform_semicircleReal_zero_one_boundary hx
  have hnorm : Tendsto
      (fun ε : ℝ ↦ ‖resolventTransform (semicircleReal 0 1)
        ((x : ℂ) + (ε : ℂ) * Complex.I)‖)
      (𝓝[>] 0) (𝓝 1) := by
    have h := continuous_norm.continuousAt.tendsto.comp hM
    change Tendsto
      (fun ε : ℝ ↦ ‖resolventTransform (semicircleReal 0 1)
        ((x : ℂ) + (ε : ℂ) * Complex.I)‖)
      (𝓝[>] 0) (𝓝 ‖c‖) at h
    simpa [hcNorm] using h
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hnorm
  change Tendsto
    (fun ε : ℝ ↦ Real.log ‖resolventTransform (semicircleReal 0 1)
      ((x : ℂ) + (ε : ℂ) * Complex.I)‖)
    (𝓝[>] 0) (𝓝 (Real.log 1)) at hlog
  simpa using hlog

private theorem tendsto_primitive_re_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦
        (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4 - 1 / 2)) := by
  let M : ℝ → ℂ := fun ε ↦
    resolventTransform (semicircleReal 0 1) ((x : ℂ) + (ε : ℂ) * Complex.I)
  let A : ℝ → ℝ := fun ε ↦ (M ε).re
  let B : ℝ → ℝ := fun ε ↦ ε * (M ε).im
  have hM := tendsto_resolventTransform_semicircleReal_zero_one_boundary hx
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (-x / 2)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hM
    change Tendsto (fun ε : ℝ ↦ (M ε).re) (𝓝[>] 0)
      (𝓝 (((-x / 2 : ℝ) : ℂ) +
        (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I).re) at h
    simpa [A] using h
  have hIm : Tendsto (fun ε : ℝ ↦ (M ε).im) (𝓝[>] 0)
      (𝓝 (Real.sqrt (1 - x ^ 2 / 4))) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp hM
    change Tendsto (fun ε : ℝ ↦ (M ε).im) (𝓝[>] 0)
      (𝓝 (((-x / 2 : ℝ) : ℂ) +
        (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I).im) at h
    simpa using h
  have hε : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hB : Tendsto B (𝓝[>] 0) (𝓝 0) := by
    have h := hε.mul hIm
    simpa [B] using h
  have hlog : Tendsto
      (fun ε : ℝ ↦ Real.log ‖M ε‖) (𝓝[>] 0) (𝓝 0) := by
    simpa [M] using tendsto_log_norm_m_boundary hx
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
      (fun ε ↦ (-(x * A ε) / 2 + B ε / 2) - Real.log ‖M ε‖)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4)) := by
    have h := (hterm₁.add hterm₂).sub hlog
    simpa using h
  have hfinal := hsum.add (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ (-1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 (-1 / 2)))
  have hEq : (fun ε : ℝ ↦ (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re) =ᶠ[𝓝[>] 0]
      fun ε ↦
        (-(x * A ε) / 2 + B ε / 2) -
          Real.log ‖M ε‖ + (-1 / 2) := by
    filter_upwards with ε
    let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
    let a : ℝ := (M ε).re
    let b : ℝ := (M ε).im
    have hfirst :
        (-(z * M ε) / 2).re = -(x * a) / 2 + ε * b / 2 := by
      simp [z, a, b, M, Complex.mul_re]
      ring
    have hprimitive :
        (primitive z).re =
          (-(z * M ε) / 2).re - Real.log ‖M ε‖ - 1 / 2 := by
      rw [primitive_re]
      simp [z, M, m]
    rw [hprimitive, hfirst]
    ring
  have h' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hfinal
  have hlimit : x ^ 2 / 4 + (-1 / 2) = x ^ 2 / 4 - 1 / 2 := by ring
  rw [← hlimit]
  exact h'

/-- The logarithmic potential of the standard semicircle law on its support. -/
private theorem integral_log_abs_sub_semicircleReal_zero_one (x : ℝ) (hx : x ∈ Icc (-2) 2) :
    (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1) = x ^ 2 / 4 - 1 / 2 := by
  let H : ℝ → ℝ := fun ε ↦
    ∫ y : ℝ, Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1
  have hH : Tendsto H (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1)) := by
    simpa [H] using tendsto_integral_log_norm_sub_semicircleReal 0 x (v := 1) (by norm_num)
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
        by
          simpa [m] using
            integral_log_norm_sub_semicircleReal 0 (v := 1) (by norm_num) hz
      _ = (primitive z).re := (primitive_re z).symm
  have hprimitive := tendsto_primitive_re_boundary hx
  have hH' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hprimitive
  exact tendsto_nhds_unique hH hH'

/-- The logarithmic potential of a positive-variance semicircle law on its support. -/
theorem integral_log_abs_sub_semicircleReal (a x : ℝ) {v : ℝ≥0} (hv : 0 < v)
    (hx : x ∈ Icc (a - 2 * Real.sqrt v) (a + 2 * Real.sqrt v)) :
    (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v) =
      (x - a) ^ 2 / (4 * (v : ℝ)) + Real.log (Real.sqrt v) - 1 / 2 := by
  let s : ℝ := Real.sqrt v
  let x₀ : ℝ := (x - a) / s
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hs2 : s ^ 2 = v := by
    dsimp [s]
    exact Real.sq_sqrt v.coe_nonneg
  have hvar : Real.toNNReal (s ^ 2) * (1 : ℝ≥0) = v := by
    apply NNReal.coe_injective
    simp [hs2]
  have hmap : (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
      semicircleReal a v := by
    calc
      (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
          semicircleReal (a + s * 0) (Real.toNNReal (s ^ 2) * 1) :=
        map_affine_semicircleReal 0 a s 1
      _ = semicircleReal a v := by simp [hvar]
  have hx₀ : x₀ ∈ Icc (-2) 2 := by
    constructor
    · apply (le_div_iff₀ hs).2
      dsimp [x₀, s]
      nlinarith [hx.1]
    · apply (div_le_iff₀ hs).2
      dsimp [x₀, s]
      nlinarith [hx.2]
  have hmapInt :
      (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v) =
        ∫ y : ℝ, Real.log |x - (a + s * y)| ∂semicircleReal 0 1 := by
    rw [← hmap]
    rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  have hlogInt : Integrable (fun y : ℝ ↦ Real.log |x₀ - y|) (semicircleReal 0 1) :=
    integrable_log_abs_sub_semicircleReal x₀ 0 1
  have hne : ∀ᵐ y : ℝ ∂semicircleReal 0 1, y ≠ x₀ := by
    let _ := nullSingletonClass_semicircleReal 0 (by norm_num : (0 : ℝ≥0) < 1)
    exact (semicircleReal 0 1).ae_ne x₀
  have hkernel : (fun y : ℝ ↦ Real.log |x - (a + s * y)|) =ᵐ[semicircleReal 0 1]
      fun y ↦ Real.log s + Real.log |x₀ - y| := by
    filter_upwards [hne] with y hy
    have hfactor : x - (a + s * y) = s * (x₀ - y) := by
      dsimp [x₀]
      field_simp
      ring
    rw [hfactor, abs_mul, abs_of_pos hs,
      Real.log_mul (ne_of_gt hs)
        (ne_of_gt (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hy))))]
  calc
    ∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v =
        ∫ y : ℝ, (Real.log s + Real.log |x₀ - y|) ∂semicircleReal 0 1 := by
          rw [hmapInt]
          exact integral_congr_ae hkernel
    _ = Real.log s + ∫ y : ℝ, Real.log |x₀ - y| ∂semicircleReal 0 1 := by
      rw [integral_add (integrable_const _) hlogInt]
      simp
    _ = Real.log s + x₀ ^ 2 / 4 - 1 / 2 := by
      rw [integral_log_abs_sub_semicircleReal_zero_one x₀ hx₀]
      ring
    _ = (x - a) ^ 2 / (4 * (v : ℝ)) + Real.log s - 1 / 2 := by
      change Real.log s + ((x - a) / s) ^ 2 / 4 - 1 / 2 =
        (x - a) ^ 2 / (4 * (v : ℝ)) + Real.log s - 1 / 2
      rw [← hs2]
      field_simp [ne_of_gt hs]
      ring

end TauCeti.Probability
