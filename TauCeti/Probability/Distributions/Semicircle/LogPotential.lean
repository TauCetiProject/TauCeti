/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The logarithmic potential of the semicircle law

For the standard law `semicircleReal 0 1`, the logarithmic potential is
`x ^ 2 / 4 - 1 / 2` on `[-2, 2]`. Hence the effective potential
`x ^ 2 / 2 - 2 ∫ log |x - y| dμ(y)` of the Gaussian beta gas is constant on the support. This is
the equality part of the equilibrium criterion; the effective-potential inequality outside the
support is also needed for the full characterization.

## Main results

* `TauCeti.Probability.integrable_log_abs_sub_semicircleReal`: the logarithmic kernel is
  integrable against the semicircle law.
* `TauCeti.Probability.tendsto_integral_log_norm_sub_semicircleReal`: convergence to the real-axis
  potential at every real point, including outside the support.
* `TauCeti.Probability.integral_log_abs_sub_semicircleReal_zero_one`: the logarithmic potential
  on the support of the standard semicircle law.

## Implementation notes

Let `m z = ∫ (y - z)⁻¹ dμ(y)` be the resolvent transform, which satisfies `m² + z m + 1 = 0` and
has positive imaginary part in the upper half-plane. The complex logarithmic potential
`H z = ∫ log (z - y) dμ(y)` has derivative `-m`, as does the primitive
`-z m / 2 - log (-m) - 1 / 2`; the two agree up to a constant whose real part vanishes at
infinity. Taking real parts gives the potential in the upper half-plane. The quadratic equation
identifies the boundary values of `m` on `(-2, 2)`, whose modulus is `1` and whose real part is
`-x / 2`. The potential is continuous up to the real axis by dominated convergence.

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
  have hy' : |y - a| ≤ 2 * Real.sqrt v := by
    rcases hy with ⟨hylo, hyhi⟩
    rw [abs_le]
    constructor <;> linarith
  have habs := abs_sub_abs_le_abs_sub y a
  have hcomm : |y - a| = |a - y| := abs_sub_comm y a
  rw [hcomm] at hy'
  linarith

/-- The Stieltjes transform of the standard semicircle law. -/
local notation "m" => resolventTransform (semicircleReal 0 1)

private def primitive (z : ℂ) : ℂ :=
  -(z * m z) / 2 - Complex.log (-(m z)) - 1 / 2

section UpperHalfPlane

variable {z : ℂ}

private theorem mem_slitPlane_neg_m (hz : 0 < z.im) : -(m z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have hm := (im_resolventTransform_pos (μ := semicircleReal 0 1)
    (IsProbabilityMeasure.ne_zero _) hz).ne'
  simpa using neg_ne_zero.mpr hm

private theorem m_ne_zero (hz : 0 < z.im) : m z ≠ 0 := by
  intro hm
  have h : m z * m z + z * m z + 1 = 0 := by
    simpa using ((eq_resolventTransform_semicircleReal_iff (a := 0) (v := 1) hz).1 rfl).2
  rw [hm] at h
  norm_num at h

private theorem deriv_m_quad (hz : 0 < z.im) {d : ℂ} (hdm : HasDerivAt m d z) :
    d * m z + m z * d + m z + z * d = 0 := by
  have him : 0 < (2 * m z + z).im := by
    have hm := im_resolventTransform_pos (μ := semicircleReal 0 1)
      (IsProbabilityMeasure.ne_zero _) hz
    have heq : (2 * m z + z).im = 2 * (m z).im + z.im := by simp
    rw [heq]
    linarith
  have hne : 2 * m z + z ≠ 0 := fun h ↦ him.ne' (by rw [h, zero_im])
  have hderiv : d = -m z / (2 * m z + z) := by
    rw [← hdm.deriv]
    simpa using deriv_resolventTransform_semicircleReal (a := 0) (v := 1) hz
  have h := (eq_div_iff hne).mp hderiv
  linear_combination h

private theorem hasDerivAt_primitive (hz : 0 < z.im) :
    HasDerivAt primitive (-m z) z := by
  obtain ⟨d, hdm⟩ : ∃ d, HasDerivAt m d z :=
    ⟨_, hasDerivAt_resolventTransform_of_im_ne_zero (μ := semicircleReal 0 1) hz.ne'⟩
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
    have hq1 : m z * m z + z * m z + 1 = 0 := by
      simpa using ((eq_resolventTransform_semicircleReal_iff (a := 0) (v := 1) hz).1 rfl).2
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
    convert (Measure.hasDerivAt_integral_clog_sub_of_im_ne_zero (semicircleReal 0 1)
      isCompact_Icc (by simpa using restrict_Icc_semicircleReal 0 1) hu.ne').sub
        (hasDerivAt_primitive hu) using 1
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
      isCompact_Icc (by simpa using restrict_Icc_semicircleReal 0 1) hz.ne',
    Measure.integral_log_norm_sub_eq_re_of_im_ne_zero (semicircleReal 0 1)
      isCompact_Icc (by simpa using restrict_Icc_semicircleReal 0 1) hw.ne'] using h

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

end UpperHalfPlane

private theorem tendsto_primitive_re_boundary {x : ℝ} (hx : x ∈ Icc (-2) 2) :
    Tendsto
      (fun ε : ℝ ↦ (primitive ((x : ℂ) + (ε : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (x ^ 2 / 4 - 1 / 2)) := by
  let c : ℂ := ((-x / 2 : ℝ) : ℂ) + (Real.sqrt (1 - x ^ 2 / 4) : ℂ) * Complex.I
  have hcSq : Complex.normSq c = 1 := by
    have hx0 : ‖(-x / 2 : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_neg]
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 <|
        abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hform : c =
        ((-x / 2 : ℝ) : ℂ) +
          Complex.I * (Real.sqrt (1 - (-x / 2) ^ 2) : ℝ) := by
      dsimp [c]
      rw [show ((Real.sqrt (1 - x ^ 2 / 4) : ℝ) : ℂ) * Complex.I =
          Complex.I * (Real.sqrt (1 - x ^ 2 / 4) : ℝ) by ring,
        show (1 - x ^ 2 / 4 : ℝ) = 1 - (-x / 2) ^ 2 by ring]
    rw [hform]
    exact Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hx0
  have hcNorm : ‖c‖ = 1 := by
    rw [Complex.norm_def, hcSq, Real.sqrt_one]
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
      _ = (primitive z).re := by
        exact real_logPotential_eq_primitive_re hz
  have hprimitive := tendsto_primitive_re_boundary hx
  have hH' := Filter.Tendsto.congr' (EventuallyEq.symm hEq) hprimitive
  exact tendsto_nhds_unique hH hH'

end TauCeti.Probability
