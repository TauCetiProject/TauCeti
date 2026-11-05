/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp

/-!
# Weighted energy estimates for the plane-vortex adjoint

Multiplication by a real weight gives an exact localization identity for the gauge-fixed
vortex adjoint. Its error is the squared gradient of the weight, with coefficient one.
Combining this identity with exterior coercivity gives the weighted energy estimate for
`L_x L_x*`, with margin `a - c²` when the squared exterior mass is `a` and the logarithmic
weight has gradient bounded by `c`. In particular, exponential weights with rate below
`1/2` are allowed sufficiently far out on a vortex with unit-modulus end.

All estimates here concern compactly supported classical test fields. They are the energy
estimates used for exponentially decaying inputs, not a construction of a completed inverse
or a uniform spectral gap over the noncompact vortex moduli space.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter
open scoped Laplacian Topology RealInnerProductSpace

variable {x η : ℂ → EuclideanSpace ℝ (Fin 4)} {w : ℂ → ℝ}

/-- Exact localization of the squared adjoint norm. The zeroth-order vortex coefficients
cancel, and the principal symbol contributes precisely `|dw|² |η|²`. No equation for `x`
is needed. -/
theorem norm_sq_gaugeFixedAdjoint_fun_smul (x : ℂ → EuclideanSpace ℝ (Fin 4)) {z : ℂ}
    (hw : DifferentiableAt ℝ w z) (hη : DifferentiableAt ℝ η z) :
    ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2 =
      ⟪gaugeFixedAdjoint x (fun t ↦ w t ^ 2 • η t) z, gaugeFixedAdjoint x η z⟫ +
        ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2 := by
  have hp : fderiv ℝ (fun t ↦ w t ^ 2) z = (2 * w z) • fderiv ℝ w z := by
    simpa using (hw.hasFDerivAt.pow 2).fderiv
  rw [gaugeFixedAdjoint_fun_smul x hw hη,
    gaugeFixedAdjoint_fun_smul x (hw.fun_pow 2) hη, hp, gaugeFixedAdjointSymbol_smul_left]
  simp only [norm_add_sq_real, inner_add_left, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_sq_gaugeFixedAdjointSymbol, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  ring

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

private theorem integrable_weightGradientError (hw : ContDiff ℝ 1 w)
    (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun z ↦ ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2) μ := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  exact (by fun_prop : Continuous (fun z ↦
    ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2)).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))

/-- The integrated localization identity: the weighted pairing with `L_x L_x*` equals
the localized adjoint energy minus the exact weight-gradient error. -/
theorem integral_norm_sq_gaugeFixedAdjoint_fun_smul
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hw : ContDiff ℝ 1 w) :
    (∫ z, ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2 ∂μ) =
      (∫ z, w z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) +
        ∫ z, ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2 ∂μ := by
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hc
  have hi : Integrable (fun z ↦
      ⟪gaugeFixedAdjoint x (fun t ↦ w t ^ 2 • η t) z, gaugeFixedAdjoint x η z⟫) μ :=
    ((continuous_gaugeFixedAdjoint hx.continuous ((hw.pow 2).smul hη₁)).inner
      hA.continuous).integrable_of_hasCompactSupport
        (hAc.mono fun z hz he ↦ hz (by simp [he]))
  have he := integrable_weightGradientError (μ := μ) hw hη.continuous hc
  simp_rw [norm_sq_gaugeFixedAdjoint_fun_smul x (hw.differentiable (by norm_num) _)
    (hη.differentiable (by norm_num) _)]
  rw [integral_add hi he]
  congr 1
  have hg := integral_inner_gaugeFixedOperator (μ := μ) hx.continuous hA hAc
    ((hw.pow 2).smul hη₁)
  simpa only [Pi.smul_def', real_inner_smul_right, real_inner_comm] using hg.symm

/-- A real weight whose logarithmic gradient is bounded by `c` reduces the exterior
squared mass from `a` to `a - c²`. The pairing is with the actual second-order operator
`L_x L_x*`; no inverse or range assertion is assumed. -/
theorem mul_integral_mul_norm_sq_le_integral_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hw : ContDiff ℝ 2 w) (hsol : ∀ z, η z ≠ 0 → equation x z = 0)
    {a c : ℝ} (ha : a ≤ 1 / 4)
    (hP : ∀ z, η z ≠ 0 → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hdw : ∀ z, η z ≠ 0 →
      ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2) :
    (a - c ^ 2) * (∫ z, w z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
      ∫ z, w z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hloc := mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ)
    hx (hw.smul hη) hc.smul_left (fun z hz ↦ hsol z (fun he ↦ hz (by simp [he]))) ha
    (fun z hz ↦ hP z (fun he ↦ hz (by simp [he])))
  simp only [Pi.smul_def'] at hloc
  rw [integral_norm_sq_gaugeFixedAdjoint_fun_smul hx hη hc (hw.of_le (by norm_num))] at hloc
  have hi : Integrable (fun z ↦ w z ^ 2 * ‖η z‖ ^ 2) μ :=
    ((hw.continuous.pow 2).mul (hη.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have he := integrable_weightGradientError (μ := μ)
    (hw.of_le (by norm_num)) hη.continuous hc
  have hb := integral_mono he (hi.const_mul (c ^ 2)) fun z ↦
    by
      by_cases hz : η z = 0
      · simp [hz]
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hdw z hz) (sq_nonneg ‖η z‖)
  rw [integral_const_mul] at hb
  have hn (z : ℂ) : ‖w z • η z‖ ^ 2 = w z ^ 2 * ‖η z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [hn] at hloc
  nlinarith

/-- On a vortex with unit-modulus end, the smooth exponential weight
`exp(c √(1 + |z|²))` has exterior energy margin `a - c²` for every `a < 1/4`.
The margin is positive when `c² < a`. The same radius works for every compactly
supported `C²` test field vanishing on the indicated disc. -/
theorem exists_exterior_integral_exp_mul_norm_sq_le_integral_exp_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a c : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → (∀ z, ‖z‖ ≤ R → η z = 0) →
      (a - c ^ 2) *
          (∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  obtain ⟨R, hR₀, hR⟩ := exists_exterior_lt_mass hlim ha
  have hw : ContDiff ℝ 2 (fun z : ℂ ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))) :=
    contDiff_exp_mul_sqrt_one_add_norm_sq c
  have hdw (z : ℂ) :
      ‖fderiv ℝ (fun t : ℂ ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z‖ ^ 2 ≤
        c ^ 2 * Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 := by
    have hb := norm_fderiv_exp_mul_sqrt_one_add_norm_sq_le c z
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [mul_pow, sq_abs] using hs
  refine ⟨R, hR₀, fun η hη hηc hzero ↦ ?_⟩
  have hP (z : ℂ) (hz : η z ≠ 0) : a ≤ x z 2 ^ 2 + x z 3 ^ 2 :=
    (hR z (lt_of_not_ge fun h ↦ hz (hzero z h))).le
  exact mul_integral_mul_norm_sq_le_integral_mul_inner_gaugeFixedOperator (μ := μ)
    hx hη hηc hw (fun z _ ↦ hsol z) ha.le hP (fun z _ ↦ hdw z)

end TauCeti.Vortex
