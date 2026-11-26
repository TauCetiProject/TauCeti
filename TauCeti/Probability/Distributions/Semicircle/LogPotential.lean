/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Real.Inequalities
import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Basic.Complex.OfRealSub

/-!
# The logarithmic potential of the semicircle law

For a positive-variance semicircle law `semicircleReal a v`, the logarithmic potential on its
support is `(x - a) ^ 2 / (4 * v) + log (√v) - 1 / 2`. The standard law `semicircleReal 0 1`
therefore has potential `x ^ 2 / 4 - 1 / 2` on `[-2, 2]`. Hence the effective potential
`x ^ 2 / 2 - 2 ∫ log |x - y| dμ(y)` of the Gaussian beta gas is constant on the support. This is
the equality part of the equilibrium criterion; the effective-potential inequality outside the
support is also needed for the full characterization.

## Main results

* `TauCeti.Probability.integrable_log_abs_sub_semicircleReal`: the logarithmic kernel is
  integrable against the semicircle law.
* `TauCeti.Probability.integral_log_norm_sub_semicircleReal_of_im_pos`: the upper-half-plane
  potential formula for any semicircle law, including zero variance.
* `TauCeti.Probability.tendsto_integral_log_norm_sub_semicircleReal`: convergence to the real-axis
  potential at every real point, including outside the support.
* `TauCeti.Probability.integral_log_abs_sub_semicircleReal_zero_one`: the logarithmic potential
  on the support of the standard semicircle law.
* `TauCeti.Probability.integral_log_abs_sub_semicircleReal_of_mem_Icc`: the logarithmic potential
  on the support of any positive-variance semicircle law.

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
    apply Measure.integrable_log_abs_sub_of_le_smul_volume_restrict
      (semicircleReal a v) x l u (ENNReal.ofReal (Real.pi * Real.sqrt v)⁻¹)
      ENNReal.ofReal_ne_top
    have hrestr : (semicircleReal a v).restrict (Icc l u) = semicircleReal a v :=
      restrict_Icc_semicircleReal a v
    rw [← hrestr]
    rw [← Measure.restrict_smul]
    exact Measure.restrict_mono_measure (semicircleReal_le_smul_volume a hv) _

private theorem ae_ne_semicircleReal (a x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    ∀ᵐ y ∂semicircleReal a v, y ≠ x := by
  let _ := nullSingletonClass_semicircleReal a hv
  exact (semicircleReal a v).ae_ne x

/-- The logarithmic kernel converges in integral to its real-axis value for a positive-variance
semicircle law. -/
theorem tendsto_integral_log_norm_sub_semicircleReal (a x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    Tendsto
      (fun ε : ℝ ↦ ∫ y : ℝ,
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal a v)
      (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v)) := by
  let R : ℝ := |a| + 2 * Real.sqrt v
  refine Measure.tendsto_integral_log_norm_sub_of_ae_abs_le (semicircleReal a v) x R ?_
    (ae_ne_semicircleReal a x hv) (integrable_log_abs_sub_semicircleReal x a v)
  filter_upwards [ae_mem_Icc_semicircleReal a v] with y hy
  exact Real.abs_le_abs_add_of_mem_Icc a y (2 * Real.sqrt v) hy

/-- The Stieltjes transform of the standard semicircle law. -/
local notation "m" => resolventTransform (semicircleReal 0 1)

private def primitive (z : ℂ) : ℂ :=
  -(z * m z) / 2 - Complex.log (-(m z)) - 1 / 2

section UpperHalfPlane

variable {z : ℂ}

private theorem restrict_standardSemicircleReal :
    (semicircleReal 0 1).restrict (Icc (-2) 2) = semicircleReal 0 1 := by
  simpa using restrict_Icc_semicircleReal 0 1

private theorem hasDerivAt_m (hz : 0 < z.im) : ∃ d, HasDerivAt m d z := by
  exact ⟨_, hasDerivAt_resolventTransform (μ := semicircleReal 0 1) z
    (Complex.notMem_image_ofReal_of_im_ne_zero hz.ne')⟩

private theorem mem_slitPlane_neg_m (hz : 0 < z.im) : -(m z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have hm := (im_resolventTransform_semicircleReal_zero_one_pos hz).ne'
  simpa using neg_ne_zero.mpr hm

private theorem m_ne_zero (hz : 0 < z.im) : m z ≠ 0 := by
  intro hm
  have h := resolventTransform_semicircleReal_zero_one_quadratic_eq_zero hz.ne'
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
    simpa using resolventTransform_semicircleReal_zero_one_quadratic_eq_zero (by
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
    have hq1 := resolventTransform_semicircleReal_zero_one_quadratic_eq_zero hz.ne'
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
    convert (Measure.hasDerivAt_integral_clog_sub_of_im_pos (semicircleReal 0 1)
      isCompact_Icc restrict_standardSemicircleReal hu).sub (hasDerivAt_primitive hu) using 1
    simp
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

private def realPrimitiveCore (p : ℂ × ℂ) : ℝ :=
  (-(p.1 * p.2) / 2).re - Real.log ‖p.2‖ - 1 / 2

private theorem continuousAt_realPrimitiveCore {p : ℂ × ℂ} (hp : p.2 ≠ 0) :
    ContinuousAt realPrimitiveCore p := by
  unfold realPrimitiveCore
  fun_prop (disch := exact norm_ne_zero_iff.mpr hp)

private theorem real_logPotential_sub_primitive_is_const {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) - (primitive z).re =
      (∫ y : ℝ, Real.log ‖w - y‖ ∂semicircleReal 0 1) - (primitive w).re := by
  have h := congrArg Complex.re (logPotential_sub_primitive_is_const hz hw)
  simpa only [Complex.sub_re,
    Measure.integral_log_norm_sub_eq_re_of_im_ne_zero (semicircleReal 0 1)
      isCompact_Icc restrict_standardSemicircleReal hz.ne',
    Measure.integral_log_norm_sub_eq_re_of_im_ne_zero (semicircleReal 0 1)
      isCompact_Icc restrict_standardSemicircleReal hw.ne'] using h

private theorem tendsto_primitive_re_sub_log_atTop :
    Tendsto (fun t : ℝ ↦ (primitive ((t : ℂ) * Complex.I)).re - Real.log t)
      atTop (𝓝 0) := by
  have hcomplex : Tendsto
      (fun t : ℝ ↦ t * Complex.I * m (t * Complex.I)) atTop (𝓝 (-1 : ℂ)) := by
    simpa using
      (MeasureTheory.tendsto_mul_I_mul_resolventTransform
        (μ := semicircleReal 0 1))
  have h := (continuousAt_realPrimitiveCore (p := ((1 : ℂ), -1)) (by norm_num)).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds hcomplex)
  have heq : ∀ᶠ t : ℝ in atTop,
      (primitive ((t : ℂ) * Complex.I)).re - Real.log t =
        realPrimitiveCore (1, (t : ℂ) * Complex.I * m (t * Complex.I)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hzt : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht
    have hnorm : ‖(t : ℂ) * Complex.I * m ((t : ℂ) * Complex.I)‖ =
        t * ‖m ((t : ℂ) * Complex.I)‖ := by
      rw [norm_mul, norm_mul]
      simp [abs_of_pos ht]
    rw [primitive_re]
    simp only [realPrimitiveCore, one_mul, hnorm,
      Real.log_mul (ne_of_gt ht) (norm_ne_zero_iff.mpr (m_ne_zero hzt))]
    ring
  have h' := Filter.Tendsto.congr' (EventuallyEq.symm heq) h
  simpa [realPrimitiveCore, Function.comp_def] using h'

private theorem real_logPotential_eq_primitive_re {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) = (primitive z).re := by
  let C := (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal 0 1) - (primitive z).re
  have hG : Tendsto
      (fun t : ℝ ↦
        (∫ y : ℝ, Real.log ‖(t : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1) -
          (primitive ((t : ℂ) * Complex.I)).re) atTop (𝓝 0) := by
    have hH := Measure.tendsto_integral_log_norm_mul_I_sub_log_atTop (semicircleReal 0 1) 2 (by
      filter_upwards [ae_mem_Icc_semicircleReal 0 1] with y hy
      apply abs_le.mpr
      simpa using hy)
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

private theorem integral_log_norm_sub_semicircleReal_affine
    (a : ℝ) {v : ℝ≥0} (hv : 0 < v) (z : ℂ)
    (hne : ∀ᵐ y : ℝ ∂semicircleReal 0 1, (z - a) / Real.sqrt v - y ≠ 0)
    (hint : Integrable (fun y : ℝ ↦ Real.log ‖(z - a) / Real.sqrt v - y‖)
      (semicircleReal 0 1)) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
      Real.log (Real.sqrt v) +
        ∫ y : ℝ, Real.log ‖(z - a) / Real.sqrt v - y‖ ∂semicircleReal 0 1 := by
  let s : ℝ := Real.sqrt v
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hmap : (semicircleReal 0 1).map (fun y : ℝ ↦ a + s * y) =
      semicircleReal a v := map_standardSemicircleReal a v
  rw [← hmap]
  exact Measure.integral_log_norm_sub_map_affine _ a hs z hne hint

private theorem integral_log_norm_sub_semicircleReal_of_im_pos_of_pos
    (a : ℝ) {v : ℝ≥0} (hv : 0 < v) {z : ℂ}
    (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
      ( -((z - a) * resolventTransform (semicircleReal a v) z) / 2).re -
        Real.log ‖resolventTransform (semicircleReal a v) z‖ - 1 / 2 := by
  let s : ℝ := Real.sqrt v
  let w : ℂ := (z - a) / s
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hw : 0 < w.im := by
    simpa only [w, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero] using
      div_pos hz hs
  have hlogInt :
      Integrable (fun y : ℝ ↦ Real.log ‖w - y‖) (semicircleReal 0 1) :=
    Measure.integrable_log_norm_sub_of_im_ne_zero (semicircleReal 0 1)
      isCompact_Icc restrict_standardSemicircleReal hw.ne'
  have hne : ∀ᵐ y : ℝ ∂semicircleReal 0 1, w - y ≠ 0 := by
    filter_upwards with y
    exact sub_ne_zero.mpr
      (Ne.symm (sub_ne_zero.mp (Complex.ofReal_sub_ne_zero_of_im_ne_zero hw.ne' y)))
  have hscale :
      (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
        Real.log s + ∫ y : ℝ, Real.log ‖w - y‖ ∂semicircleReal 0 1 := by
    exact integral_log_norm_sub_semicircleReal_affine a hv z hne hlogInt
  have hstd := log_norm_eq_primitive_re hw
  have hRT : resolventTransform (semicircleReal a v) z =
      (s : ℂ)⁻¹ * resolventTransform (semicircleReal 0 1) w := by
    simpa [s, w] using resolventTransform_semicircleReal_eq_standard a hv z
  have harg : z - a = (s : ℂ) * w := by
    dsimp [w]
    exact (mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hs.ne')).symm
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
  calc
    ∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v =
        Real.log s + ∫ y : ℝ, Real.log ‖w - y‖ ∂semicircleReal 0 1 := hscale
    _ = Real.log s + (-(w * m w) / 2).re - Real.log ‖m w‖ - 1 / 2 := by
      rw [hstd]
      ring
    _ = ( -((z - a) * resolventTransform (semicircleReal a v) z) / 2).re -
        Real.log ‖resolventTransform (semicircleReal a v) z‖ - 1 / 2 := by
      rw [hRT, hprod, hlog]
      ring_nf

/-- In the upper half-plane, the logarithmic potential of a semicircle law is expressed by its
resolvent transform, including when its variance is zero. -/
theorem integral_log_norm_sub_semicircleReal_of_im_pos (a : ℝ) (v : ℝ≥0) {z : ℂ}
    (hz : 0 < z.im) :
    (∫ y : ℝ, Real.log ‖z - y‖ ∂semicircleReal a v) =
      ( -((z - a) * resolventTransform (semicircleReal a v) z) / 2).re -
        Real.log ‖resolventTransform (semicircleReal a v) z‖ - 1 / 2 := by
  rcases eq_zero_or_pos v with rfl | hv
  · have hza : z - (a : ℂ) ≠ 0 := sub_ne_zero.mpr
      (Ne.symm (sub_ne_zero.mp (Complex.ofReal_sub_ne_zero_of_im_ne_zero hz.ne' a)))
    have hmul : (z - (a : ℂ)) * ((a : ℂ) - z)⁻¹ = -1 := by
      have hsub : (a : ℂ) - z = -(z - a) := by ring
      rw [hsub, inv_neg, mul_neg, mul_inv_cancel₀ hza]
    rw [semicircleReal_zero_var, integral_dirac, resolventTransform_dirac]
    simp only [resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap, hmul, norm_inv,
      Real.log_inv]
    rw [norm_sub_rev (a : ℂ) z]
    norm_num
  · exact integral_log_norm_sub_semicircleReal_of_im_pos_of_pos a hv hz

private theorem tendsto_primitive_re_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦ (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4 - 1 / 2)) := by
  let c : ℂ := ((-x / 2 : ℝ) : ℂ) + (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I
  have hrad : 0 ≤ 1 - x ^ 2 / 4 := by
    have hx2 : x ^ 2 ≤ 4 := by
      have h := sq_le_sq' hx.1 hx.2
      norm_num at h
      exact h
    linarith
  have hcSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_apply]
    simp [c]
    nlinarith [Real.sq_sqrt hrad]
  have hcNorm : ‖c‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq c
    rw [hcSq] at h
    nlinarith [norm_nonneg c]
  have hM : Tendsto (fun ε : ℝ ↦ resolventTransform (semicircleReal 0 1)
      ((x : ℂ) + (ε : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 c) :=
    tendsto_resolventTransform_semicircleReal_zero_one_of_mem_Icc hx
  have hε : Tendsto (fun ε : ℝ ↦ (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0))
  have hz : Tendsto (fun ε : ℝ ↦ (x : ℂ) + (ε : ℂ) * Complex.I)
      (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    simpa using tendsto_const_nhds.add (hε.mul_const Complex.I)
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcNorm]; norm_num)
  have h := (continuousAt_realPrimitiveCore (p := ((x : ℂ), c)) hc).tendsto.comp
    (hz.prodMk_nhds hM)
  have hval : realPrimitiveCore ((x : ℂ), c) = x ^ 2 / 4 - 1 / 2 := by
    simp only [realPrimitiveCore]
    rw [hcNorm, Real.log_one, sub_zero]
    simp [c, Complex.mul_re]
    ring
  rw [hval] at h
  simpa only [Function.comp_def, realPrimitiveCore, primitive_re] using h

/-- The logarithmic potential of the standard semicircle law on its support. -/
theorem integral_log_abs_sub_semicircleReal_zero_one (x : ℝ) (hx : x ∈ Icc (-2) 2) :
    (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1) = x ^ 2 / 4 - 1 / 2 := by
  let H : ℝ → ℝ := fun ε ↦
    ∫ y : ℝ, Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ∂semicircleReal 0 1
  have hH : Tendsto H (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, Real.log |x - y| ∂semicircleReal 0 1)) := by
    simpa [H] using
      tendsto_integral_log_norm_sub_semicircleReal 0 x (v := 1) (by norm_num)
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
          simpa using
            integral_log_norm_sub_semicircleReal_of_im_pos 0 1 hz
      _ = (primitive z).re := (primitive_re z).symm
  have hprimitive := tendsto_primitive_re_boundary hx
  have hH' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hprimitive
  exact tendsto_nhds_unique hH hH'

/-- The logarithmic potential of a positive-variance semicircle law on its support. -/
theorem integral_log_abs_sub_semicircleReal_of_mem_Icc (a x : ℝ) {v : ℝ≥0} (hv : 0 < v)
    (hx : x ∈ Icc (a - 2 * Real.sqrt v) (a + 2 * Real.sqrt v)) :
    (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v) =
      (x - a) ^ 2 / (4 * (v : ℝ)) + Real.log (Real.sqrt v) - 1 / 2 := by
  let s : ℝ := Real.sqrt v
  let x₀ : ℝ := (x - a) / s
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hs2 : s ^ 2 = v := by
    dsimp [s]
    exact Real.sq_sqrt v.coe_nonneg
  have hx₀ : x₀ ∈ Icc (-2) 2 := sub_div_sqrt_mem_Icc_of_mem_Icc hv hx
  have hlogInt : Integrable (fun y : ℝ ↦ Real.log |x₀ - y|) (semicircleReal 0 1) :=
    integrable_log_abs_sub_semicircleReal x₀ 0 1
  have hne : ∀ᵐ y : ℝ ∂semicircleReal 0 1, y ≠ x₀ := by
    exact ae_ne_semicircleReal 0 x₀ (by norm_num)
  have hne' : ∀ᵐ y : ℝ ∂semicircleReal 0 1,
      ((x : ℂ) - a) / Real.sqrt v - y ≠ 0 := by
    filter_upwards [hne] with y hy
    have hxy : x₀ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    exact_mod_cast hxy
  have hlogInt' : Integrable
      (fun y : ℝ ↦ Real.log ‖((x : ℂ) - a) / Real.sqrt v - y‖)
      (semicircleReal 0 1) := by
    simpa [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real,
      Real.norm_eq_abs, x₀, s] using hlogInt
  have hscale :
      (∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v) =
        Real.log s + ∫ y : ℝ, Real.log |x₀ - y| ∂semicircleReal 0 1 := by
    simpa [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real,
      Real.norm_eq_abs, x₀, s] using
      integral_log_norm_sub_semicircleReal_affine a hv (x : ℂ) hne' hlogInt'
  calc
    ∫ y : ℝ, Real.log |x - y| ∂semicircleReal a v =
        Real.log s + ∫ y : ℝ, Real.log |x₀ - y| ∂semicircleReal 0 1 := hscale
    _ = Real.log s + x₀ ^ 2 / 4 - 1 / 2 := by
      rw [integral_log_abs_sub_semicircleReal_zero_one x₀ hx₀]
      ring
    _ = (x - a) ^ 2 / (4 * (v : ℝ)) + Real.log s - 1 / 2 := by
      dsimp only [x₀]
      rw [← hs2]
      field_simp [ne_of_gt hs]
      ring

end TauCeti.Probability
