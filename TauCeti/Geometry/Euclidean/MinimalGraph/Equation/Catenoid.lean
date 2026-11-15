/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
import all TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The upper half-catenoid as a minimal graph

For the height `arcosh ρ` on `ρ > 1`, the radial minimal-graph flux is constant.
The two-dimensional graph flux is the inverse-square radial field and has zero divergence.

## References

* T. H. Colding and W. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
-/

public noncomputable section

open scoped Gradient Topology

namespace TauCeti.MinimalGraph


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The divergence of a radial scalar multiple of the identity map. -/
theorem trace_fderiv_radial_smul (c : E → ℝ) (x : E)
    (hc : DifferentiableAt ℝ c x) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y : E ↦ c y • y) x).toLinearMap =
      (Module.finrank ℝ E : ℝ) * c x + fderiv ℝ c x x := by
  change LinearMap.trace ℝ E (fderiv ℝ (fun y : E ↦ c y • id y) x).toLinearMap = _
  rw [fderiv_fun_smul hc differentiableAt_id]
  simp [LinearMap.trace_smulRight, LinearMap.trace_id, mul_comm]

/-- The vector field `x / ‖x‖²` on a Euclidean plane. -/
def inverseSquareRadialField (x : E) : E := (‖x‖ ^ 2)⁻¹ • x

omit [FiniteDimensional ℝ E] in
private theorem fderiv_inv_norm_sq_self {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ (‖y‖ ^ 2)⁻¹) x x =
      -(2 : ℝ) * (‖x‖ ^ 2)⁻¹ := by
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have h := ((hasFDerivAt_inv (𝕜 := ℝ) hn).comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).fderiv
  change (fderiv ℝ ((fun t : ℝ ↦ t⁻¹) ∘ fun y : E ↦ ‖y‖ ^ 2) x) x = _
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
  rw [real_inner_self_eq_norm_sq]
  simp only [smul_eq_mul, two_smul]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnorm]
  have hprod : ‖x‖ ^ 4 * (‖x‖⁻¹) ^ 4 = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero 4 hnorm)
  nlinarith [hprod]

/-- In dimension two, the inverse-square radial field is divergence-free away from zero. -/
theorem trace_fderiv_inverseSquareRadialField_eq_zero (hE : Module.finrank ℝ E = 2)
    {x : E} (hx : x ≠ 0) :
    LinearMap.trace ℝ E (fderiv ℝ inverseSquareRadialField x).toLinearMap = 0 := by
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hc : DifferentiableAt ℝ (fun y : E ↦ (‖y‖ ^ 2)⁻¹) x :=
    (hasStrictFDerivAt_norm_sq x).differentiableAt.inv hn
  change LinearMap.trace ℝ E
    (fderiv ℝ (fun y : E ↦ (‖y‖ ^ 2)⁻¹ • y) x).toLinearMap = 0
  rw [trace_fderiv_radial_smul _ x hc, hE, fderiv_inv_norm_sq_self hx]
  ring

/-- The radial minimal-graph flux of the upper half-catenoid. -/
def catenoidRadialFlux (ρ : ℝ) : ℝ :=
  ρ * (Real.sqrt (ρ ^ 2 - 1))⁻¹ /
    Real.sqrt (1 + ((Real.sqrt (ρ ^ 2 - 1))⁻¹) ^ 2)

/-- The derivative of the upper half-catenoid height on its graph domain. -/
theorem hasDerivAt_arcosh_of_one_lt {ρ : ℝ} (hρ : 1 < ρ) :
    HasDerivAt Real.arcosh (Real.sqrt (ρ ^ 2 - 1))⁻¹ ρ :=
  Real.hasDerivAt_arcosh hρ

/-- The radial flux is defined using the actual derivative of `arcosh` on `ρ > 1`. -/
theorem catenoidRadialFlux_eq_deriv {ρ : ℝ} (hρ : 1 < ρ) :
    catenoidRadialFlux ρ = ρ * deriv Real.arcosh ρ /
      Real.sqrt (1 + (deriv Real.arcosh ρ) ^ 2) := by
  rw [(hasDerivAt_arcosh_of_one_lt hρ).deriv]
  rfl

/-- The radial flux is identically one above the neck of the catenoid. -/
theorem catenoidRadialFlux_eq_one {ρ : ℝ} (hρ : 1 < ρ) :
    catenoidRadialFlux ρ = 1 := by
  have hsq : 0 < ρ ^ 2 - 1 := by nlinarith
  let s := Real.sqrt (ρ ^ 2 - 1)
  have hs : 0 < s := Real.sqrt_pos.2 hsq
  have hs2 : s ^ 2 = ρ ^ 2 - 1 := Real.sq_sqrt hsq.le
  have hsqrt : Real.sqrt (1 + s⁻¹ ^ 2) = ρ / s := by
    have hnonneg : 0 ≤ ρ / s := div_nonneg (by linarith) hs.le
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) hnonneg).2
    field_simp
    nlinarith
  rw [catenoidRadialFlux, show Real.sqrt (ρ ^ 2 - 1) = s from rfl, hsqrt]
  field_simp

/-- The radial flux has zero derivative on the half-catenoid graph domain. -/
theorem deriv_catenoidRadialFlux_eq_zero {ρ : ℝ} (hρ : 1 < ρ) :
    deriv catenoidRadialFlux ρ = 0 := by
  have heq : catenoidRadialFlux =ᶠ[𝓝 ρ] fun _ ↦ (1 : ℝ) :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (show ρ ∈ Set.Ioi (1 : ℝ) from hρ))
      (fun _ ht ↦ catenoidRadialFlux_eq_one ht)
  exact ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- The upper half-catenoid height on the exterior of the unit ball. -/
def upperCatenoidHeight (x : E) : ℝ := Real.arcosh ‖x‖

private theorem hasGradientAt_norm_of_one_lt {x : E} (hx : 1 < ‖x‖) :
    HasGradientAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert TauCeti.hasFDerivAt_norm_of_ne (norm_ne_zero_iff.mp (by linarith : ‖x‖ ≠ 0)) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

private theorem hasGradientAt_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    HasGradientAt upperCatenoidHeight
      ((Real.sqrt (‖x‖ ^ 2 - 1))⁻¹ • (‖x‖⁻¹ • x)) x := by
  exact (hasDerivAt_arcosh_of_one_lt hx).comp_hasGradientAt
    (hasGradientAt_norm_of_one_lt hx)

/-- The normalized gradient of the upper half-catenoid is the inverse-square radial field. -/
theorem areaWeight_smul_gradient_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    areaWeight upperCatenoidHeight x • ∇ upperCatenoidHeight x =
      inverseSquareRadialField x := by
  let ρ : ℝ := ‖x‖
  let a : ℝ := (Real.sqrt (ρ ^ 2 - 1))⁻¹
  have hρ : ρ ≠ 0 := by dsimp [ρ]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hgrad : ∇ upperCatenoidHeight x = (a * ρ⁻¹) • x := by
    rw [(hasGradientAt_upperCatenoidHeight hx).gradient]
    simp only [smul_smul]
    rfl
  have hnorm : ‖∇ upperCatenoidHeight x‖ = a := by
    rw [(hasGradientAt_upperCatenoidHeight hx).gradient, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (lt_trans zero_lt_one hx)]
    rw [inv_mul_cancel₀ hρ, mul_one]
  have hscalar : (Real.sqrt (1 + a ^ 2))⁻¹ * (a * ρ⁻¹) = (ρ ^ 2)⁻¹ := by
    have hsqrt : Real.sqrt (1 + a ^ 2) ≠ 0 := by positivity
    have hflux := catenoidRadialFlux_eq_one hx
    change ρ * a / Real.sqrt (1 + a ^ 2) = 1 at hflux
    field_simp at hflux ⊢
    nlinarith [hflux]
  dsimp only [inverseSquareRadialField]
  rw [areaWeight_eq_inv_sqrt, hnorm, hgrad]
  simp only [smul_smul]
  rw [hscalar]

/-- The upper half-catenoid graph has the inverse-square radial area flux. -/
theorem areaFlux_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    areaFlux upperCatenoidHeight x = inverseSquareRadialField x := by
  change areaWeight upperCatenoidHeight x • ∇ upperCatenoidHeight x =
    inverseSquareRadialField x
  exact areaWeight_smul_gradient_upperCatenoidHeight hx

/-- The upper half-catenoid solves the two-dimensional minimal graph equation. -/
theorem fluxDivergence_upperCatenoidHeight (hE : Module.finrank ℝ E = 2)
    {x : E} (hx : 1 < ‖x‖) : fluxDivergence upperCatenoidHeight x = 0 := by
  have hlocal : areaFlux upperCatenoidHeight =ᶠ[𝓝 x] inverseSquareRadialField := by
    have hopen : IsOpen {y : E | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact areaFlux_upperCatenoidHeight hy
  change LinearMap.trace ℝ E
    (fderiv ℝ (areaFlux upperCatenoidHeight) x).toLinearMap = 0
  rw [hlocal.fderiv_eq]
  exact trace_fderiv_inverseSquareRadialField_eq_zero hE
    (norm_ne_zero_iff.mp (by linarith : ‖x‖ ≠ 0))

end TauCeti.MinimalGraph
