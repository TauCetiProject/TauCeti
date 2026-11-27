/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Logarithmic cutoffs on the plane

A point of the plane has capacity zero: there are cutoffs equal to `1` near the point and to `0`
far away whose Dirichlet energy `∫ ‖dχ‖²` is as small as we like. In the real coordinates
`z ∈ ℝ × ℝ` of `w ∈ ℂ` used throughout the Floer theory of Tau Ceti, with `|w|` the Euclidean norm
`‖Complex.equivRealProdCLM.symm z‖`:

* `∫_{ε ≤ |w| ≤ δ} |w|⁻² = 2π log (δ / ε)` for `0 < ε ≤ δ`
  (`TauCeti.Complex.integral_indicator_Icc_inv_sq_norm_equivRealProdCLM_symm`), by integration in
  polar coordinates (`MeasureTheory.integral_fun_norm_addHaar`);
* for `0 < ε` and `4 ε ≤ δ`, the cutoff `χ(w) = 1 - ψ(|w|)` built from the logarithmic cutoff
  profile `ψ = TauCeti.logCutoffProfile ε δ` is smooth, equal to `1` on `|w| ≤ ε` and to `0` on
  `|w| ≥ δ`, and `|dχ(w)| ≤ 2 c₀ / (|w| log (δ / ε))` with `c₀ = TauCeti.logCutoffConst`, so its
  Dirichlet energy is at most `8π c₀² / log (δ / ε)`
  (`TauCeti.Complex.exists_contDiff_logCutoff`).

The factor `2` bounds the derivative of `z ↦ |w|` in the sup norm of `ℝ × ℝ`. The energy tends to
`0` as `δ / ε → ∞`, while the cutoffs with linear profile have energy bounded below independently
of the scale. Read through the inversion `w ↦ w⁻¹`, the same cutoffs cut off a neighbourhood of
the point at infinity of the Riemann sphere.
-/

public section

open Set Filter MeasureTheory Real
open scoped Topology ContDiff

namespace TauCeti.Complex

/-- **The integral of `|w|⁻²` over an annulus.** For `0 < ε ≤ δ`, the integral of `|w|⁻²` over the
annulus `ε ≤ |w| ≤ δ` of the plane, in real coordinates, is `2π log (δ / ε)`. -/
theorem integral_indicator_Icc_inv_sq_norm_equivRealProdCLM_symm {ε δ : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    ∫ z : ℝ × ℝ, (Icc ε δ).indicator (fun r ↦ (r ^ 2)⁻¹) ‖Complex.equivRealProdCLM.symm z‖ =
      2 * π * Real.log (δ / ε) := by
  set g : ℝ → ℝ := (Icc ε δ).indicator fun r ↦ (r ^ 2)⁻¹
  -- Pass to `ℂ`, where the integral of a radial function is a one-dimensional integral.
  have hC := (Complex.volume_preserving_equiv_real_prod).integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ × ℝ ↦ g ‖Complex.equivRealProdCLM.symm z‖)
  simp only [Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM,
    ContinuousLinearEquiv.symm_apply_apply] at hC
  rw [← hC, integral_fun_norm_addHaar (volume : Measure ℂ) g]
  simp only [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • g y = Real.log (δ / ε) := by
    have hcongr : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • g y =
        ∫ y in Ioi (0 : ℝ), (Icc ε δ).indicator (fun r ↦ r⁻¹) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
      by_cases h : y ∈ Icc ε δ
      · simp only [g, indicator_of_mem h, smul_eq_mul, Nat.add_one_sub_one, pow_one]
        field_simp
      · simp [g, indicator_of_notMem h]
    rw [hcongr, setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 fun y (hy : y ∈ Icc ε δ) ↦ (hε.trans_le hy.1 : y ∈ Ioi 0),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hεδ,
      integral_inv_of_pos hε (hε.trans_le hεδ)]
  rw [hrad]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal zero_le_one,
    one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- The Euclidean norm `|w|` of the plane is `2`-Lipschitz in the sup norm of `ℝ × ℝ`. -/
private theorem lipschitzWith_two_norm_equivRealProdCLM_symm :
    LipschitzWith 2 fun z : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z‖ :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [Real.dist_eq, dist_eq_norm]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← map_sub]
    simpa using norm_equivRealProdCLM_symm_le_two_mul (a - b)

/-- The logarithmic cutoff `1 - ψ(|w|)` of the plane, for the logarithmic cutoff profile
`ψ = TauCeti.logCutoffProfile ε δ`. -/
private noncomputable def planeLogCutoff (ε δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - logCutoffProfile ε δ ‖Complex.equivRealProdCLM.symm z‖

/-- The logarithmic cutoff is `1` near every point of `|w| < ε`. -/
private theorem planeLogCutoff_eventuallyEq_one {ε δ : ℝ} (h2 : 2 * ε ≤ δ) {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z‖ < ε) : planeLogCutoff ε δ =ᶠ[𝓝 z] fun _ ↦ 1 := by
  have hNc := Complex.equivRealProdCLM.symm.continuous.norm
  filter_upwards [(isOpen_lt hNc continuous_const).mem_nhds hz] with w hw
  simp [planeLogCutoff, logCutoffProfile_eq_zero_of_le h2 (le_of_lt hw)]

/-- The logarithmic cutoff is `0` near every point of `|w| > δ`. -/
private theorem planeLogCutoff_eventuallyEq_zero {ε δ : ℝ} (hε : 0 < ε) (h2 : 2 * ε ≤ δ)
    {z : ℝ × ℝ} (hz : δ < ‖Complex.equivRealProdCLM.symm z‖) :
    planeLogCutoff ε δ =ᶠ[𝓝 z] fun _ ↦ 0 := by
  have hNc := Complex.equivRealProdCLM.symm.continuous.norm
  filter_upwards [(isOpen_lt continuous_const hNc).mem_nhds hz] with w hw
  simp [planeLogCutoff, logCutoffProfile_eq_one_of_ge hε h2 (le_of_lt hw)]

/-- Away from `w = 0` the logarithmic cutoff is the profile composed with the smooth norm, and near
`w = 0` it is constant, so it is smooth. -/
private theorem contDiff_planeLogCutoff {ε δ : ℝ} (hε : 0 < ε) (h2 : 2 * ε ≤ δ) :
    ContDiff ℝ ∞ (planeLogCutoff ε δ) := contDiff_iff_contDiffAt.2 fun z ↦ by
  rcases lt_or_ge ‖Complex.equivRealProdCLM.symm z‖ ε with hz | hz
  · exact contDiffAt_const.congr_of_eventuallyEq (planeLogCutoff_eventuallyEq_one h2 hz)
  · exact contDiffAt_const.sub ((contDiff_logCutoffProfile (by linarith)).contDiffAt.comp z
      ((contDiffAt_norm ℝ (norm_pos_iff.1 (hε.trans_le hz))).comp z
        Complex.equivRealProdCLM.symm.contDiff.contDiffAt))

/-- On the annulus `ε ≤ |w|`, the derivative of the logarithmic cutoff has norm at most
`2 c₀ / (|w| log (δ / ε))`. -/
private theorem norm_fderiv_planeLogCutoff_le {ε δ : ℝ} (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    {z : ℝ × ℝ} (hz : ε ≤ ‖Complex.equivRealProdCLM.symm z‖) :
    ‖fderiv ℝ (planeLogCutoff ε δ) z‖ ≤
      2 * (logCutoffConst / (‖Complex.equivRealProdCLM.symm z‖ * Real.log (δ / ε))) := by
  set N : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  have h2 : 2 * ε ≤ δ := by linarith
  have hN0 : 0 < N z := hε.trans_le hz
  have hNd : ContDiffAt ℝ 1 N z := (contDiffAt_norm ℝ (norm_pos_iff.1 hN0)).comp z
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  have hNf : HasFDerivAt N (fderiv ℝ N z) z := (hNd.differentiableAt one_ne_zero).hasFDerivAt
  have hψ := (contDiff_logCutoffProfile (ε := ε) (by linarith : δ ≠ 0)).differentiable (by simp)
  have hcomp : HasFDerivAt (planeLogCutoff ε δ)
      (-(deriv (logCutoffProfile ε δ) (N z) • fderiv ℝ N z)) z := by
    have h1 := (hasFDerivAt_const (1 : ℝ) z).sub ((hψ (N z)).hasDerivAt.comp_hasFDerivAt z hNf)
    rwa [zero_sub] at h1
  rw [hcomp.fderiv, norm_neg, norm_smul, Real.norm_of_nonneg
    (deriv_logCutoffProfile_nonneg hε h2 _), mul_comm]
  exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ lipschitzWith_two_norm_equivRealProdCLM_symm)
    (deriv_logCutoffProfile_le hε h4 hN0.le) (deriv_logCutoffProfile_nonneg hε h2 _)
    zero_le_two

/-- Pointwise, the squared derivative of the logarithmic cutoff is at most
`(2 c₀ / log (δ / ε))² |w|⁻²` on the annulus `ε ≤ |w| ≤ δ`, and `0` off it. -/
private theorem sq_norm_fderiv_planeLogCutoff_le {ε δ : ℝ} (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (z : ℝ × ℝ) :
    ‖fderiv ℝ (planeLogCutoff ε δ) z‖ ^ 2 ≤ (2 * logCutoffConst / Real.log (δ / ε)) ^ 2 *
      (Icc ε δ).indicator (fun r ↦ (r ^ 2)⁻¹) ‖Complex.equivRealProdCLM.symm z‖ := by
  have h2 : 2 * ε ≤ δ := by linarith
  by_cases hz : ‖Complex.equivRealProdCLM.symm z‖ ∈ Icc ε δ
  · rw [indicator_of_mem hz]
    have hN0 : 0 < ‖Complex.equivRealProdCLM.symm z‖ := hε.trans_le hz.1
    calc ‖fderiv ℝ (planeLogCutoff ε δ) z‖ ^ 2
        ≤ (2 * (logCutoffConst / (‖Complex.equivRealProdCLM.symm z‖ * Real.log (δ / ε)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_planeLogCutoff_le hε h4 hz.1) 2
      _ = _ := by field_simp
  · rw [indicator_of_notMem hz, mul_zero]
    rcases not_and_or.1 hz with h | h
    · simp [(planeLogCutoff_eventuallyEq_one h2 (not_le.1 h)).fderiv_eq]
    · simp [(planeLogCutoff_eventuallyEq_zero hε h2 (not_le.1 h)).fderiv_eq]

/-- **Logarithmic cutoffs on the plane.** For `0 < ε` and `4 ε ≤ δ` there is a smooth function `χ`
with values in `[0, 1]`, equal to `1` on the disc `|w| ≤ ε` and to `0` on `|w| ≥ δ`, whose
derivative vanishes on `|w| < ε` and whose Dirichlet energy is at most `8π c₀² / log (δ / ε)`,
for `c₀ = TauCeti.logCutoffConst`. -/
theorem exists_contDiff_logCutoff {ε δ : ℝ} (hε : 0 < ε) (h4 : 4 * ε ≤ δ) :
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ z, χ z ∈ Icc 0 1) ∧
      (∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ ε → χ z = 1) ∧
      (∀ z, δ ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0) ∧
      (∀ z, ‖Complex.equivRealProdCLM.symm z‖ < ε → fderiv ℝ χ z = 0) ∧
      Integrable (fun z ↦ ‖fderiv ℝ χ z‖ ^ 2) ∧
      ∫ z, ‖fderiv ℝ χ z‖ ^ 2 ≤ 8 * π * logCutoffConst ^ 2 / Real.log (δ / ε) := by
  have h2 : 2 * ε ≤ δ := by linarith
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hχs := contDiff_planeLogCutoff hε h2
  set c := (2 * logCutoffConst / Real.log (δ / ε)) ^ 2
  have hI := integral_indicator_Icc_inv_sq_norm_equivRealProdCLM_symm hε (by linarith : ε ≤ δ)
  have hIi : Integrable fun z ↦
      (Icc ε δ).indicator (fun r ↦ (r ^ 2)⁻¹) ‖Complex.equivRealProdCLM.symm z‖ :=
    Integrable.of_integral_ne_zero (by rw [hI]; positivity)
  have hDi : Integrable fun z ↦ ‖fderiv ℝ (planeLogCutoff ε δ) z‖ ^ 2 :=
    ((hχs.continuous_fderiv (by simp)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le δ) fun z hz ↦ by
        simp [(planeLogCutoff_eventuallyEq_zero hε h2 (not_le.1 hz)).fderiv_eq])
  refine ⟨planeLogCutoff ε δ, hχs, fun z ↦ ⟨?_, ?_⟩, fun z hz ↦ ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_, hDi, ?_⟩
  · have := logCutoffProfile_le_one hε h2 ‖Complex.equivRealProdCLM.symm z‖
    simp only [planeLogCutoff]
    linarith
  · have := logCutoffProfile_nonneg hε h2 ‖Complex.equivRealProdCLM.symm z‖
    simp only [planeLogCutoff]
    linarith
  · simp [planeLogCutoff, logCutoffProfile_eq_zero_of_le h2 hz]
  · simp [planeLogCutoff, logCutoffProfile_eq_one_of_ge hε h2 hz]
  · rw [(planeLogCutoff_eventuallyEq_one h2 hz).fderiv_eq, fderiv_const_apply]
  calc ∫ z, ‖fderiv ℝ (planeLogCutoff ε δ) z‖ ^ 2
      ≤ ∫ z, c * (Icc ε δ).indicator (fun r ↦ (r ^ 2)⁻¹) ‖Complex.equivRealProdCLM.symm z‖ :=
        integral_mono hDi (hIi.const_mul c) (sq_norm_fderiv_planeLogCutoff_le hε h4)
    _ = 8 * π * logCutoffConst ^ 2 / Real.log (δ / ε) := by
        rw [integral_const_mul, hI]
        have := hΛ.ne'
        simp only [c]
        field_simp
        ring

end TauCeti.Complex
