/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.Vorticity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Calculus.Gradient

/-!
# Checks: rigid rotation of the plane

On an oriented plane with rotation `J` by `π/2`, the rigid rotation `u x = J x` with pressure
`p x = ‖x‖² / 2` is a stationary solution of the Euler equations: `(u·∇)u = J (J x) = −x = −∇p`
(`Orientation.add_fderiv_rightAngleRotation_add_gradient_eq_zero`), and `u` is divergence-free
(`Orientation.trace_rightAngleRotation`). Its scalar vorticity is `2`
(`Orientation.scalarVorticity_rightAngleRotation`), the sign fixed by the convention
`ω = ∂₁u₂ − ∂₂u₁` for the counterclockwise rotation `(−x₂, x₁)`. The pressure Poisson equation
`−Δp = trace ((∇u)²) = trace (J²) = −2` then recovers `Δ (‖x‖² / 2) = 2`
(`Orientation.laplacian_norm_sq_div_two`).
-/

public section

open Module
open scoped Gradient InnerProductSpace Laplacian

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

local notation "J" => o.rightAngleRotation

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- The rotation by `π/2` is trace-free: the rigid rotation is divergence-free. -/
theorem trace_rightAngleRotation :
    LinearMap.trace ℝ E ((J : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 := by
  simp [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]

/-- **Rigid rotation solves the Euler equations.** The stationary velocity `u x = J x` with
pressure `p x = ‖x‖² / 2` satisfies `∂ₜu + (u·∇)u + ∇p = 0` everywhere. -/
theorem add_fderiv_rightAngleRotation_add_gradient_eq_zero (t : ℝ) (x : E) :
    deriv (fun _ : ℝ ↦ J x) t + fderiv ℝ J x (J x) + ∇ (fun y : E ↦ (‖y‖ ^ 2 / 2 : ℝ)) x = 0 := by
  have hp : ∇ (fun y : E ↦ (‖y‖ ^ 2 / 2 : ℝ)) x = x := by
    simpa [div_eq_inv_mul] using TauCeti.gradient_mul_norm_sq_add (E := E) 1 0 x
  simp [LinearIsometryEquiv.fderiv, hp]

variable (E) in
/-- **The pressure Poisson equation for rigid rotation.** Applied to the rigid rotation of an
oriented plane, `−Δp = trace ((∇u)²)` gives `Δ (‖x‖² / 2) = 2`, the dimension of the plane. -/
theorem laplacian_norm_sq_div_two (x : E) : Δ (fun y : E ↦ (‖y‖ ^ 2 / 2 : ℝ)) x = 2 := by
  let o : Orientation ℝ E (Fin 2) := (Module.finBasisOfFinrankEq ℝ E Fact.out).orientation
  have h := TauCeti.neg_laplacian_eq_trace_fderiv_mul_fderiv (u := fun _ y ↦ o.rightAngleRotation y)
    (p := fun _ y ↦ (‖y‖ ^ 2 / 2 : ℝ)) (t := 0) (x := x)
    ((o.rightAngleRotation : E →L[ℝ] E).contDiff.comp contDiff_snd).contDiffAt
    ((contDiff_norm_sq ℝ).div_const 2).contDiffAt
    (.of_forall fun y ↦ o.add_fderiv_rightAngleRotation_add_gradient_eq_zero 0 y)
    (.of_forall fun _ ↦ by rw [LinearIsometryEquiv.fderiv]; exact o.trace_rightAngleRotation)
  have hJJ : (o.rightAngleRotation : E →L[ℝ] E) * (o.rightAngleRotation : E →L[ℝ] E) = -1 := by
    ext y
    simp
  rw [LinearIsometryEquiv.fderiv, hJJ] at h
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.toLinearMap_neg, map_neg,
    ContinuousLinearMap.coe_id, LinearMap.trace_id, (Fact.out : finrank ℝ E = 2)] at h
  linarith

end Orientation
