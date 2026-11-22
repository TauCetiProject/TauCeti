/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Rescaling smooth bumps

A smooth bump `φ : ContDiffBump (0 : E)` is the fixed profile `someContDiffBumpBase E` for the
ratio `φ.rOut / φ.rIn` of its radii, read at scale `φ.rIn`. So two bumps with the same ratio of
radii are rescalings of each other (`ContDiffBump.apply_eq_apply_smul_of_rOut_div_rIn_eq`), and so
are their normalizations with respect to an additive Haar measure
(`ContDiffBump.normed_eq_mul_normed_smul_of_rOut_div_rIn_eq`). The usual mollifiers
`ε⁻ⁿ ρ (x / ε)`, such as the bumps `ContDiffBump.shrinking` of radii `R / (2 (n + 1))` and
`R / (n + 1)`, are families of this kind.

Quantities invariant under rescaling therefore agree along such a family. The one recorded here is
the first moment `∫ ‖t‖ ‖∂ᵥ (φ.normed μ) t‖ dt` of a directional derivative of the normalized
bump (`ContDiffBump.lintegral_eNorm_mul_eNorm_fderiv_normed_apply_eq`): it bounds the commutator of
mollification with a first-order operator with Lipschitz coefficients, and its invariance makes
these commutators uniformly bounded along a family of mollifiers. The first moment of a directional
derivative of any `C¹` compactly supported function is finite
(`HasCompactSupport.lintegral_eNorm_mul_eNorm_fderiv_apply_ne_top`).

## Main results

* `ContDiffBump.apply_eq_apply_smul_of_rOut_div_rIn_eq`,
  `ContDiffBump.normed_eq_mul_normed_smul_of_rOut_div_rIn_eq`: bumps with the same ratio of radii
  are rescalings of each other.
* `ContDiffBump.fderiv_normed_apply_eq_of_rOut_div_rIn_eq`: the corresponding rescaling of the
  directional derivatives.
* `ContDiffBump.lintegral_eNorm_mul_eNorm_fderiv_normed_apply_eq`: the first moment of a
  directional derivative of a normalized bump only depends on the ratio of its radii.
* `HasCompactSupport.lintegral_eNorm_mul_eNorm_fderiv_apply_ne_top`: this first moment is finite.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first moment `∫ ‖t‖ ‖∂ᵥ ρ t‖ dt` of a directional derivative of a `C¹` compactly supported
function is finite. -/
theorem HasCompactSupport.lintegral_eNorm_mul_eNorm_fderiv_apply_ne_top [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {ρ : E → ℝ}
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (v : E) :
    ∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ ρ t v‖ₑ ∂μ ≠ ∞ := by
  have hc : Continuous fun t : E ↦ ‖t‖ * fderiv ℝ ρ t v :=
    continuous_norm.mul (hρ.continuous_fderiv_apply_const one_ne_zero v)
  have hs : HasCompactSupport fun t : E ↦ ‖t‖ * fderiv ℝ ρ t v :=
    (hρc.fderiv_apply (𝕜 := ℝ) v).mul_left
  simpa [HasFiniteIntegral, eNorm_mul] using
    (hc.integrable_of_hasCompactSupport hs (μ := μ)).hasFiniteIntegral.ne

namespace ContDiffBump

/-- Two bumps centred at the origin with the same ratio of radii are rescalings of each other:
`φ x = ψ ((ψ.rIn / φ.rIn) • x)`. -/
theorem apply_eq_apply_smul_of_rOut_div_rIn_eq [HasContDiffBump E] (φ ψ : ContDiffBump (0 : E))
    (h : φ.rOut / φ.rIn = ψ.rOut / ψ.rIn) (x : E) :
    φ x = ψ ((ψ.rIn / φ.rIn) • x) := by
  rw [φ.apply, ψ.apply, h, sub_zero, sub_zero, smul_smul,
    show ψ.rIn⁻¹ * (ψ.rIn / φ.rIn) = φ.rIn⁻¹ by field_simp [ψ.rIn_pos.ne']]

variable [FiniteDimensional ℝ E]

/-- A normalized bump is a rescaling of any other normalized bump with the same ratio of radii:
with `c = ψ.rIn / φ.rIn`, `φ.normed μ x = c ^ n * ψ.normed μ (c • x)`, where `n = dim E`. -/
theorem normed_eq_mul_normed_smul_of_rOut_div_rIn_eq [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (φ ψ : ContDiffBump (0 : E))
    (h : φ.rOut / φ.rIn = ψ.rOut / ψ.rIn) (x : E) :
    φ.normed μ x = (ψ.rIn / φ.rIn) ^ Module.finrank ℝ E * ψ.normed μ ((ψ.rIn / φ.rIn) • x) := by
  have hc : 0 < ψ.rIn / φ.rIn := div_pos ψ.rIn_pos φ.rIn_pos
  have hint : ∫ y, φ y ∂μ = ((ψ.rIn / φ.rIn) ^ Module.finrank ℝ E)⁻¹ * ∫ y, ψ y ∂μ := by
    simp_rw [apply_eq_apply_smul_of_rOut_div_rIn_eq φ ψ h]
    rw [Measure.integral_comp_smul_of_nonneg μ (fun y ↦ ψ y) _ (hR := hc.le), smul_eq_mul]
  rw [normed_def, normed_def, hint, apply_eq_apply_smul_of_rOut_div_rIn_eq φ ψ h]
  have := ψ.integral_pos (μ := μ)
  field_simp

/-- The derivative of a normalized bump in a direction `v`, rescaled: with `c = ψ.rIn / φ.rIn`
and `n = dim E`, `∂ᵥ (φ.normed μ) x = c ^ (n + 1) * ∂ᵥ (ψ.normed μ) (c • x)` whenever `φ` and `ψ`
have the same ratio of radii. -/
theorem fderiv_normed_apply_eq_of_rOut_div_rIn_eq [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (φ ψ : ContDiffBump (0 : E))
    (h : φ.rOut / φ.rIn = ψ.rOut / ψ.rIn) (x v : E) :
    fderiv ℝ (φ.normed μ) x v = (ψ.rIn / φ.rIn) ^ (Module.finrank ℝ E + 1) *
      fderiv ℝ (ψ.normed μ) ((ψ.rIn / φ.rIn) • x) v := by
  set c := ψ.rIn / φ.rIn
  have heq : φ.normed μ = fun y ↦ c ^ Module.finrank ℝ E * ψ.normed μ (c • y) :=
    funext (normed_eq_mul_normed_smul_of_rOut_div_rIn_eq φ ψ h)
  have hd : HasFDerivAt (fun y : E ↦ ψ.normed μ (c • y))
      ((fderiv ℝ (ψ.normed μ) (c • x)).comp (c • ContinuousLinearMap.id ℝ E)) x :=
    ((ψ.contDiff_normed (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul c)
  rw [heq, ((hd.const_mul (c ^ Module.finrank ℝ E))).fderiv]
  simp only [smul_apply, comp_apply, id_apply, map_smul, smul_eq_mul, pow_succ]
  ring

/-- **The first moment of the derivative of a normalized bump only depends on the ratio of its
radii.** If `φ` and `ψ` have the same ratio `rOut / rIn`, then
`∫ ‖t‖ ‖∂ᵥ (φ.normed μ) t‖ dt = ∫ ‖t‖ ‖∂ᵥ (ψ.normed μ) t‖ dt`. -/
theorem lintegral_eNorm_mul_eNorm_fderiv_normed_apply_eq [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (φ ψ : ContDiffBump (0 : E))
    (h : φ.rOut / φ.rIn = ψ.rOut / ψ.rIn) (v : E) :
    ∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ (φ.normed μ) t v‖ₑ ∂μ =
      ∫⁻ t, ‖t‖ₑ * ‖fderiv ℝ (ψ.normed μ) t v‖ₑ ∂μ := by
  set c := ψ.rIn / φ.rIn
  have hc : 0 < c := div_pos ψ.rIn_pos φ.rIn_pos
  set n := Module.finrank ℝ E
  set w : E → ℝ≥0∞ := fun s ↦ ‖s‖ₑ * ‖fderiv ℝ (ψ.normed μ) s v‖ₑ
  -- Pointwise, the integrand for `φ` is `c ^ n` times the integrand for `ψ` at `c • t`.
  have hpt (t : E) : ‖t‖ₑ * ‖fderiv ℝ (φ.normed μ) t v‖ₑ = ‖c ^ n‖ₑ * w (c • t) := by
    rw [fderiv_normed_apply_eq_of_rOut_div_rIn_eq φ ψ h, pow_succ, eNorm_mul, eNorm_mul]
    simp only [w, eNorm_smul]
    ring
  simp_rw [hpt]
  have hone : ‖c ^ n‖ₑ * ENNReal.ofReal |(c ^ n)⁻¹| = 1 := by
    simp [Real.eNorm_eq_ofReal_abs, ENNReal.mul_inv_cancel, hc.ne']
  -- Change variables `s = c • t`.
  rw [lintegral_const_mul' _ _ eNorm_ne_top, Measure.lintegral_comp_smul μ w hc.ne', ← mul_assoc,
    hone, one_mul]

end ContDiffBump
