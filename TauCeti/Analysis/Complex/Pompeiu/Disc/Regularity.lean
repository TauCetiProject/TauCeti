/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Disc.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Regularity of the Cauchy integral of a disc indicator

The actual integral is conjugation inside the disc and a reciprocal outside it. Its two classical
Wirtinger derivatives are computed off the boundary circle.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2. This module derives the classical and
  weak regularity of the explicit disc Cauchy integral in that Cauchy–Beurling framework.
-/

public noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped Real Topology ComplexConjugate

namespace TauCeti

/-- The actual disc Cauchy integral agrees locally with conjugation in the interior. -/
theorem pi_inv_mul_integral_sub_inv_ball_eventuallyEq_conj {r : ℝ}
    {c w : ℂ} (hw : ‖w - c‖ < r) :
    (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) =ᶠ[𝓝 w]
      (fun v => conj (v - c)) := by
  have hr : 0 ≤ r := (norm_nonneg (w - c)).trans hw.le
  filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm
    continuous_const).mem_nhds hw]
    with v hv
  have hvnorm : ‖v - c‖ < r := by simpa only [Pi.sub_apply, id_eq] using hv
  rw [pi_inv_mul_integral_sub_inv_ball hr, ite_eq_left hvnorm.le]

/-- The actual disc Cauchy integral agrees locally with its reciprocal formula outside the disc. -/
theorem pi_inv_mul_integral_sub_inv_ball_eventuallyEq_div {r : ℝ} (hr : 0 ≤ r)
    {c w : ℂ} (hw : r < ‖w - c‖) :
    (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) =ᶠ[𝓝 w]
      (fun v => (r : ℂ)^2 / (v - c)) := by
  filter_upwards [(isOpen_lt continuous_const
    (continuous_id.sub continuous_const).norm).mem_nhds hw]
    with v hv
  have hvnorm : r < ‖v - c‖ := by simpa only [Pi.sub_apply, id_eq] using hv
  rw [pi_inv_mul_integral_sub_inv_ball hr, ite_eq_right (not_le.mpr hvnorm)]

/-- The real derivative of the actual disc Cauchy integral in the interior. -/
theorem hasFDerivAt_pi_inv_mul_integral_sub_inv_ball_of_lt {r : ℝ}
    {c w : ℂ} (hw : ‖w - c‖ < r) :
    HasFDerivAt (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) w := by
  have h := Complex.conjCLE.hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const c)
  simpa using h.congr_of_eventuallyEq
    (pi_inv_mul_integral_sub_inv_ball_eventuallyEq_conj hw)

/-- The complex derivative of the actual disc Cauchy integral in the exterior. -/
theorem hasDerivAt_pi_inv_mul_integral_sub_inv_ball_of_gt {r : ℝ} (hr : 0 ≤ r)
    {c w : ℂ} (hw : r < ‖w - c‖) :
    HasDerivAt (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹)
      (-(r : ℂ)^2 / (w - c)^2) w := by
  have hne : w - c ≠ 0 := norm_pos_iff.mp (hr.trans_lt hw)
  have h := ((hasDerivAt_id w).sub_const c).inv hne |>.const_mul ((r : ℂ)^2)
  simpa only [id_eq, one_mul, mul_neg_one, neg_div, div_eq_mul_inv, mul_neg, neg_mul] using
    h.congr_of_eventuallyEq
    (pi_inv_mul_integral_sub_inv_ball_eventuallyEq_div hr hw)

/-- The conjugate Wirtinger derivative recovers the disc indicator away from its boundary. -/
@[simp]
theorem conjWirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_lt {r : ℝ}
    {c w : ℂ} (hw : ‖w - c‖ < r) :
    conjWirtingerDeriv (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1 = 1 := by
  rw [conjWirtingerDeriv_apply,
    (hasFDerivAt_pi_inv_mul_integral_sub_inv_ball_of_lt hw).fderiv]
  norm_num

/-- The holomorphic Wirtinger derivative is zero inside the disc. -/
@[simp]
theorem wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_lt {r : ℝ}
    {c w : ℂ} (hw : ‖w - c‖ < r) :
    wirtingerDeriv (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1 = 0 := by
  rw [wirtingerDeriv_apply,
    (hasFDerivAt_pi_inv_mul_integral_sub_inv_ball_of_lt hw).fderiv]
  simp

/-- The exterior holomorphic derivative has the tail `-r²/(w - c)²`. -/
@[simp]
theorem wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_gt {r : ℝ} (hr : 0 ≤ r)
    {c w : ℂ} (hw : r < ‖w - c‖) :
    wirtingerDeriv (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1 =
      -(r : ℂ)^2 / (w - c)^2 := by
  have h := hasDerivAt_pi_inv_mul_integral_sub_inv_ball_of_gt hr hw
  rw [h.differentiableAt.wirtingerDeriv_eq_fderiv, fderiv_apply_one_eq_deriv, h.deriv]

/-- The conjugate Wirtinger derivative vanishes outside the disc. -/
@[simp]
theorem conjWirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_gt {r : ℝ} (hr : 0 ≤ r)
    {c w : ℂ} (hw : r < ‖w - c‖) :
    conjWirtingerDeriv (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1 = 0 := by
  have h := (hasDerivAt_pi_inv_mul_integral_sub_inv_ball_of_gt hr hw).differentiableAt
  rw [h.conjWirtingerDeriv_eq_zero]
  simp

/-- The actual normalized integral is globally bounded by the input radius. -/
theorem norm_pi_inv_mul_integral_sub_inv_ball_le {r : ℝ} (hr : 0 ≤ r) (c w : ℂ) :
    ‖(π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹‖ ≤ r := by
  rw [pi_inv_mul_integral_sub_inv_ball hr]
  split_ifs with hw
  · simpa only [norm_conj] using hw
  · have hw0 : 0 < ‖w - c‖ := hr.trans_lt (not_le.mp hw)
    rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    apply (div_le_iff₀ hw0).mpr
    nlinarith [not_le.mp hw]

/-- A point `x` of the closed disc of radius `r`: the conjugate `conj x` is within `3 ‖x - y‖` of
the inversion `r² / y` of any point `y` outside the disc. -/
private lemma norm_conj_sub_sq_div_le {r : ℝ} (hr : 0 ≤ r) (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : r < ‖y‖) :
    ‖conj x - (r : ℂ)^2/y‖ ≤ 3*‖x - y‖ := by
  have hy0 : 0 < ‖y‖ := hr.trans_lt hy
  have hyne : y ≠ 0 := norm_pos_iff.mp hy0
  have hconj : conj y * y = (‖y‖ : ℂ)^2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have heq : conj y - (r : ℂ)^2/y = (((‖y‖^2 - r^2 : ℝ) : ℂ))/y := by
    apply (eq_div_iff hyne).mpr
    rw [sub_mul, div_mul_cancel₀ _ hyne, hconj]
    push_cast
    rfl
  have hgap : ‖y‖-r ≤ ‖x - y‖ := by
    have h := norm_le_norm_add_norm_sub x y
    linarith
  have htail : ‖conj y - (r : ℂ)^2/y‖ ≤ 2 * (‖y‖-r) := by
    rw [heq, norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : 0 ≤ ‖y‖^2 - r^2)]
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  calc
    _ ≤ ‖conj x - conj y‖ + ‖conj y - (r : ℂ)^2/y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (conj x) (conj y) ((r : ℂ)^2/y)
    _ ≤ ‖x - y‖ + 2 * (‖y‖-r) := by
      rw [← map_sub, norm_conj]
      exact add_le_add le_rfl htail
    _ ≤ _ := by linarith

/-- Inversion `y ↦ r² / y` is `1`-Lipschitz on the exterior of the disc of radius `r`. -/
private lemma norm_sq_div_sub_sq_div_le {r : ℝ} (hr : 0 ≤ r) (x y : ℂ)
    (hx : r < ‖x‖) (hy : r < ‖y‖) :
    ‖(r : ℂ)^2/x - (r : ℂ)^2/y‖ ≤ ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := hr.trans_lt hx
  have hy0 : 0 < ‖y‖ := hr.trans_lt hy
  have hxn : x ≠ 0 := norm_pos_iff.mp hx0
  have hyn : y ≠ 0 := norm_pos_iff.mp hy0
  have heq : (r : ℂ)^2/x - (r : ℂ)^2/y = (r : ℂ)^2 * (y - x)/(x * y) := by
    field_simp
  rw [heq, norm_div, norm_mul, norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, norm_sub_rev y x]
  apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
  have hb : r^2 ≤ ‖x‖*‖y‖ := by nlinarith
  nlinarith [norm_nonneg (x - y)]

/-- The Cauchy integral of a disc indicator is globally Lipschitz, uniformly in the disc.
A convenient constant `3` follows directly from the two exact formulas. -/
theorem lipschitzWith_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    LipschitzWith 3 (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, pi_inv_mul_integral_sub_inv_ball hr, pi_inv_mul_integral_sub_inv_ball hr]
  norm_num only [NNReal.coe_ofNat]
  have hd : ‖(x - c) - (y - c)‖ = dist x y := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  split_ifs with hx hy hy
  · simp only [← map_sub, norm_conj, sub_sub_sub_cancel_right]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x - y)]
  · exact (norm_conj_sub_sq_div_le hr (x - c) (y - c) hx (not_le.mp hy)).trans_eq
      (by rw [hd])
  · rw [norm_sub_rev]
    exact (norm_conj_sub_sq_div_le hr (y - c) (x - c) hy (not_le.mp hx)).trans_eq
      (by rw [norm_sub_rev (y - c) (x - c), hd])
  · exact (norm_sq_div_sub_sq_div_le hr (x - c) (y - c) (not_le.mp hx)
      (not_le.mp hy)).trans (by
      rw [hd]
      nlinarith [dist_nonneg (x := x) (y := y)])

/-- The Lipschitz Cauchy integral has its actual almost everywhere derivative as native weak
derivative on the whole plane. In particular, no boundary supported distribution is discarded. -/
theorem hasWeakFDerivOn_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    HasWeakFDerivOn volume ⊤ (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹)
      (fderiv ℝ (fun w => (π : ℂ)⁻¹ * ∫ z in ball c r, (w - z)⁻¹)) :=
  ((lipschitzWith_pi_inv_mul_integral_sub_inv_ball hr c).locallyLipschitz.locallyLipschitzOn
    (s := ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ))).hasWeakFDerivOn_fderiv

/-- The actual conjugate Wirtinger derivative equals the disc indicator almost everywhere. -/
theorem ae_conjWirtingerDeriv_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    (fun w => conjWirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1) =ᵐ[volume]
      (ball c r).indicator (fun _ => (1 : ℂ)) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume c r)] with w hw
  have hne : ‖w - c‖ ≠ r := by simpa only [mem_sphere_iff_norm] using hw
  by_cases hin : ‖w - c‖ < r
  · rw [conjWirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_lt hin,
      indicator_of_mem (mem_ball_iff_norm.mpr hin)]
  · have hout : r < ‖w - c‖ := lt_of_le_of_ne (not_lt.mp hin) hne.symm
    rw [conjWirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_gt hr hout,
      indicator_of_notMem (by simpa only [mem_ball_iff_norm] using hin)]

/-- The actual holomorphic Wirtinger derivative is zero inside and has the reciprocal square
tail outside, almost everywhere. No comparison with a separate `Lp` or principal - value operator
is used. -/
theorem ae_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    (fun w => wirtingerDeriv
      (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w 1) =ᵐ[volume]
      (closedBall c r)ᶜ.indicator (fun w => -(r : ℂ)^2/(w - c)^2) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume c r)] with w hw
  have hne : ‖w - c‖ ≠ r := by simpa only [mem_sphere_iff_norm] using hw
  by_cases hin : ‖w - c‖ < r
  · rw [wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_lt hin,
      indicator_of_notMem (not_not.mpr (mem_closedBall_iff_norm.mpr hin.le))]
  · have hout : r < ‖w - c‖ := lt_of_le_of_ne (not_lt.mp hin) hne.symm
    rw [wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_gt hr hout,
      indicator_of_mem (by simpa only [mem_compl_iff, mem_closedBall_iff_norm, not_le] using hout)]

/-- The actual disc indicator Cauchy integral fails to be `C¹` at every point of a nondegenerate
boundary circle: its holomorphic Wirtinger derivative has distinct interior and exterior limits. -/
theorem not_contDiffAt_pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 < r)
    {c w : ℂ} (hw : ‖w - c‖ = r) :
    ¬ ContDiffAt ℝ 1 (fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹) w := by
  intro h
  let T : ℂ → ℂ := fun v => (π : ℂ)⁻¹ * ∫ z in ball c r, (v - z)⁻¹
  have hd : ContinuousAt (fderiv ℝ T) w := h.continuousAt_fderiv (by norm_num)
  have hcOne : ContinuousAt (fun z => fderiv ℝ T z (1 : ℂ)) w :=
    hd.clm_apply continuousAt_const
  have hcI : ContinuousAt (fun z => fderiv ℝ T z I) w := hd.clm_apply continuousAt_const
  have hc : ContinuousAt (fun z => wirtingerDeriv T z 1) w := by
    simp only [wirtingerDeriv_apply, smul_eq_mul, mul_one]
    exact continuousAt_const.mul (hcOne.sub (continuousAt_const.mul hcI))
  have hwfront : w ∈ frontier (ball c r) := by
    rw [frontier_ball c hr.ne']
    exact mem_sphere_iff_norm.mpr hw
  have hwout : w ∈ frontier (closedBall c r)ᶜ := by
    rw [frontier_compl, frontier_closedBall c hr.ne']
    exact mem_sphere_iff_norm.mpr hw
  have hzero : wirtingerDeriv T w 1 = 0 := by
    let : NeBot (𝓝[ball c r] w) :=
      mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hwfront)
    have hz : Filter.Tendsto (fun z => wirtingerDeriv T z 1) (𝓝[ball c r] w) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_lt
        (mem_ball_iff_norm.mp hz)).symm
    exact tendsto_nhds_unique (hc.mono_left nhdsWithin_le_nhds) hz
  have hne : w - c ≠ 0 := norm_pos_iff.mp (hw ▸ hr)
  have htail : wirtingerDeriv T w 1 = -(r : ℂ)^2/(w - c)^2 := by
    let : NeBot (𝓝[(closedBall c r)ᶜ] w) :=
      mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hwout)
    have hcont : ContinuousAt (fun z : ℂ => -(r : ℂ)^2/(z - c)^2) w := by
      fun_prop (disch := exact pow_ne_zero 2 hne)
    have hz : Filter.Tendsto (fun z => wirtingerDeriv T z 1) (𝓝[(closedBall c r)ᶜ] w)
        (𝓝 (-(r : ℂ)^2/(w - c)^2)) := by
      apply (hcont.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball_of_gt hr.le
        (by simpa only [mem_compl_iff, mem_closedBall_iff_norm, not_le] using hz)).symm
    exact tendsto_nhds_unique (hc.mono_left nhdsWithin_le_nhds) hz
  have ha : -(r : ℂ)^2/(w - c)^2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr.ne')))
      (pow_ne_zero 2 hne)
  exact ha (htail.symm.trans hzero)

end TauCeti
