/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.SpecialFunctions.Arcosh
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The upper half-catenoid as a minimal graph

For the height `arcosh ρ` on `ρ > 1`, the planar flux through radius `ρ` per unit angle is one.
The graph flux is `x/‖x‖²` in every dimension, with divergence `(finrank ℝ E - 2)/‖x‖²`.
On the graph domain this divergence vanishes exactly in dimension two.

## References

* T. H. Colding and W. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
-/

public noncomputable section

open scoped Gradient Topology

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Radius `ρ` times the radial component of `areaFlux` for the profile `arcosh` on `ρ > 1`:
the planar flux through radius `ρ` per unit angle. -/
def catenoidRadialFlux (ρ : ℝ) : ℝ :=
  ρ * (Real.sqrt (ρ ^ 2 - 1))⁻¹ /
    Real.sqrt (1 + ((Real.sqrt (ρ ^ 2 - 1))⁻¹) ^ 2)

theorem catenoidRadialFlux_apply (ρ : ℝ) :
    catenoidRadialFlux ρ = ρ * (Real.sqrt (ρ ^ 2 - 1))⁻¹ /
      Real.sqrt (1 + ((Real.sqrt (ρ ^ 2 - 1))⁻¹) ^ 2) := (rfl)

/-- On `ρ > 1`, the radial flux agrees with the expression using the derivative of `arcosh`. -/
theorem catenoidRadialFlux_eq_deriv {ρ : ℝ} (hρ : 1 < ρ) :
    catenoidRadialFlux ρ = ρ * deriv Real.arcosh ρ /
      Real.sqrt (1 + (deriv Real.arcosh ρ) ^ 2) := by
  rw [(Real.hasDerivAt_arcosh hρ).deriv]
  rw [catenoidRadialFlux_apply]

/-- The radial flux is identically one above the neck of the catenoid. -/
theorem catenoidRadialFlux_eq_one {ρ : ℝ} (hρ : 1 < ρ) :
    catenoidRadialFlux ρ = 1 := by
  have hsq : 0 < ρ ^ 2 - 1 := by nlinarith
  rw [catenoidRadialFlux_apply]
  set s := Real.sqrt (ρ ^ 2 - 1) with hs_def
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hsq
  have hs2 : s ^ 2 = ρ ^ 2 - 1 := by rw [hs_def]; exact Real.sq_sqrt hsq.le
  have hsqrt : Real.sqrt (1 + s⁻¹ ^ 2) = ρ / s := by
    have hnonneg : 0 ≤ ρ / s := div_nonneg (by linarith) hs.le
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) hnonneg).2
    field_simp
    linear_combination hs2
  rw [hsqrt]
  field_simp

/-- The radial flux has zero derivative on the half-catenoid graph domain. -/
theorem deriv_catenoidRadialFlux_eq_zero {ρ : ℝ} (hρ : 1 < ρ) :
    deriv catenoidRadialFlux ρ = 0 := by
  have heq : catenoidRadialFlux =ᶠ[𝓝 ρ] fun _ ↦ (1 : ℝ) :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds hρ)
      (fun _ ht ↦ catenoidRadialFlux_eq_one ht)
  exact ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- The upper half-catenoid height on the exterior of the unit ball. -/
def upperCatenoidHeight (x : E) : ℝ := Real.arcosh ‖x‖

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem upperCatenoidHeight_apply (x : E) :
    upperCatenoidHeight x = Real.arcosh ‖x‖ := (rfl)

omit [CompleteSpace E] in
/-- The upper half-catenoid height is smooth outside the unit ball. -/
theorem contDiffAt_upperCatenoidHeight {n : WithTop ℕ∞} {x : E} (hx : 1 < ‖x‖) :
    ContDiffAt ℝ n upperCatenoidHeight x :=
  (Real.contDiffAt_arcosh hx).comp x
    (contDiffAt_norm ℝ (norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))))

/-- The gradient of the upper half-catenoid height outside the unit ball. -/
theorem hasGradientAt_upperCatenoidHeight {x : E} (hx : 1 < ‖x‖) :
    HasGradientAt upperCatenoidHeight
      ((Real.sqrt (‖x‖ ^ 2 - 1))⁻¹ • (‖x‖⁻¹ • x)) x := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))
  have hn : HasGradientAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
    simpa using (TauCeti.hasFDerivAt_norm_of_ne hx0).hasGradientAt
  exact (Real.hasDerivAt_arcosh hx).comp_hasGradientAt hn

/-- The normalized gradient of the upper half-catenoid is the radial field `x / ‖x‖²`. -/
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

omit [CompleteSpace E] in
/-- The divergence of the upper half-catenoid flux in arbitrary finite dimension. -/
theorem fluxDivergence_upperCatenoidHeight [FiniteDimensional ℝ E]
    {x : E} (hx : 1 < ‖x‖) :
    fluxDivergence upperCatenoidHeight x = ((Module.finrank ℝ E : ℝ) - 2) / ‖x‖ ^ 2 := by
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hx))
  have hlocal : areaFlux upperCatenoidHeight =ᶠ[𝓝 x] ∇ (fun y : E ↦ Real.log ‖y‖) := by
    have hopen : IsOpen {y : E | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [areaFlux_upperCatenoidHeight hy]
    symm
    have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hy))
    simpa using (TauCeti.hasFDerivAt_log_norm_of_ne hy0).hasGradientAt.gradient
  rw [fluxDivergence_def, hlocal.fderiv_eq]
  have hlap := TauCeti.laplacian_eq_trace_iteratedGradientChain_one
    (fun y : E ↦ Real.log ‖y‖) x
  rw [TauCeti.iteratedGradientChain_succ, TauCeti.iteratedGradientChain_zero] at hlap
  rw [← hlap, TauCeti.laplacian_log_norm_of_ne hx0]

omit [CompleteSpace E] in
/-- The upper half-catenoid solves the two-dimensional divergence equation. -/
theorem fluxDivergence_upperCatenoidHeight_eq_zero [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 2) {x : E} (hx : 1 < ‖x‖) :
    fluxDivergence upperCatenoidHeight x = 0 := by
  rw [fluxDivergence_upperCatenoidHeight hx, hE]
  norm_num

omit [CompleteSpace E] in
/-- The upper half-catenoid solves the two-dimensional nondivergence equation. -/
theorem nondivergenceOperator_upperCatenoidHeight_eq_zero [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 2) {x : E} (hx : 1 < ‖x‖) :
    nondivergenceOperator upperCatenoidHeight x = 0 := by
  have hu : ContDiffAt ℝ 2 upperCatenoidHeight x := contDiffAt_upperCatenoidHeight hx
  have hgrad := (hu.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (fluxDivergence_eq_zero_iff hgrad).1 (fluxDivergence_upperCatenoidHeight_eq_zero hE hx)

end TauCeti.MinimalGraph
