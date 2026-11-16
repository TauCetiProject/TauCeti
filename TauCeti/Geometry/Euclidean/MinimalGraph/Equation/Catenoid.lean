/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The upper half-catenoid as a minimal graph

For the height `arcosh ρ` on `ρ > 1`, the radial minimal-graph flux is constant.
The graph flux is `x/‖x‖²` in every dimension and has zero divergence in dimension two.

## References

* T. H. Colding and W. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
-/

public noncomputable section

open scoped Gradient Topology

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The radial minimal-graph flux of the upper half-catenoid. -/
def catenoidRadialFlux (ρ : ℝ) : ℝ :=
  ρ * (Real.sqrt (ρ ^ 2 - 1))⁻¹ /
    Real.sqrt (1 + ((Real.sqrt (ρ ^ 2 - 1))⁻¹) ^ 2)

@[simp] theorem catenoidRadialFlux_apply (ρ : ℝ) :
    catenoidRadialFlux ρ = ρ * (Real.sqrt (ρ ^ 2 - 1))⁻¹ /
      Real.sqrt (1 + ((Real.sqrt (ρ ^ 2 - 1))⁻¹) ^ 2) := (rfl)

/-- The radial flux is defined using the actual derivative of `arcosh` on `ρ > 1`. -/
theorem catenoidRadialFlux_eq_deriv {ρ : ℝ} (hρ : 1 < ρ) :
    catenoidRadialFlux ρ = ρ * deriv Real.arcosh ρ /
      Real.sqrt (1 + (deriv Real.arcosh ρ) ^ 2) := by
  rw [(Real.hasDerivAt_arcosh hρ).deriv]
  rw [catenoidRadialFlux_apply]

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
    linear_combination hs2
  rw [catenoidRadialFlux_apply, hsqrt]
  field_simp
  simp only [s]

/-- The radial flux has zero derivative on the half-catenoid graph domain. -/
theorem deriv_catenoidRadialFlux_eq_zero {ρ : ℝ} (hρ : 1 < ρ) :
    deriv catenoidRadialFlux ρ = 0 := by
  have heq : catenoidRadialFlux =ᶠ[𝓝 ρ] fun _ ↦ (1 : ℝ) :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds hρ)
      (fun _ ht ↦ catenoidRadialFlux_eq_one ht)
  exact ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- The upper half-catenoid height on the exterior of the unit ball. -/
def upperCatenoidHeight (x : E) : ℝ := Real.arcosh ‖x‖

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem upperCatenoidHeight_apply (x : E) :
    upperCatenoidHeight x = Real.arcosh ‖x‖ := (rfl)

private theorem hasGradientAt_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    HasGradientAt upperCatenoidHeight
      ((Real.sqrt (‖x‖ ^ 2 - 1))⁻¹ • (‖x‖⁻¹ • x)) x := by
  have hn : HasGradientAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert TauCeti.hasFDerivAt_norm_of_ne
      (norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))) using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  exact (Real.hasDerivAt_arcosh hx).comp_hasGradientAt hn

/-- The normalized gradient of the upper half-catenoid is the inverse-square radial field. -/
theorem areaFlux_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    areaFlux upperCatenoidHeight x = (‖x‖ ^ 2)⁻¹ • x := by
  rw [areaFlux_apply]
  let ρ : ℝ := ‖x‖
  let a : ℝ := (Real.sqrt (ρ ^ 2 - 1))⁻¹
  have hρ : ρ ≠ 0 := by dsimp [ρ]; positivity
  have hgrad : ∇ upperCatenoidHeight x = (a * ρ⁻¹) • x := by
    rw [(hasGradientAt_upperCatenoidHeight hx).gradient]
    simp only [smul_smul, a, ρ]
  have hnorm : ‖∇ upperCatenoidHeight x‖ = a := by
    rw [(hasGradientAt_upperCatenoidHeight hx).gradient, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (lt_trans zero_lt_one hx)]
    rw [inv_mul_cancel₀ hρ, mul_one]
  have hscalar : (Real.sqrt (1 + a ^ 2))⁻¹ * (a * ρ⁻¹) = (ρ ^ 2)⁻¹ := by
    have hsqrt : Real.sqrt (1 + a ^ 2) ≠ 0 := by positivity
    have hflux := catenoidRadialFlux_eq_one hx
    rw [catenoidRadialFlux_apply] at hflux
    dsimp only [a, ρ] at hsqrt ⊢
    field_simp at hflux ⊢
    linear_combination hflux
  rw [areaWeight_eq_inv_sqrt, hnorm, hgrad]
  simp only [smul_smul]
  rw [hscalar]

/-- The upper half-catenoid solves the two-dimensional minimal graph equation. -/
theorem fluxDivergence_upperCatenoidHeight (hE : Module.finrank ℝ E = 2)
    {x : E} (hx : 1 < ‖x‖) : fluxDivergence upperCatenoidHeight x = 0 := by
  have hlocal : areaFlux upperCatenoidHeight =ᶠ[𝓝 x] ∇ (fun y : E ↦ Real.log ‖y‖) := by
    have hopen : IsOpen {y : E | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [areaFlux_upperCatenoidHeight hy]
    symm
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    convert TauCeti.hasFDerivAt_log_norm_of_ne
      (norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hy))) using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  rw [fluxDivergence_def, hlocal.fderiv_eq]
  have hlap := TauCeti.laplacian_eq_trace_iteratedGradientChain_one
    (fun y : E ↦ Real.log ‖y‖) x
  rw [TauCeti.iteratedGradientChain_succ, TauCeti.iteratedGradientChain_zero] at hlap
  rw [← hlap, TauCeti.laplacian_log_norm_of_ne
    (norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))), hE]
  norm_num

end TauCeti.MinimalGraph
