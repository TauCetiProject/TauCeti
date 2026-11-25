/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Symplectic.Complex.Line
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Green.Examples.CurveArea.SignedArea

/-!
# The action of the radial primitive

Let `ω` be a linear symplectic form on a finite-dimensional real vector space `V`, with its radial
primitive `λₓ(v) = ω(x, v) / 2` (`TauCeti.SymplecticForm.radialPrimitive`). Along a curve `β` in
`V` the line integral of `λ` is the symplectic action `½ ∫ ω(β, β')`
(`TauCeti.SymplecticForm.pathIntegral_radialPrimitive`). For the boundary loop of a disc it is the
symplectic area of the disc.

On `ℂ` with its standard area form, the radial primitive is `(x dy - y dx) / 2`, and around the
circle of radius `r` its integral is `π r²`, the area of the disc
(`TauCeti.pathIntegral_radialPrimitive_stdComplexSymplecticForm_circleMap`).

## Main results

* `TauCeti.SymplecticForm.pathIntegral_radialPrimitive`: `∫_β λ = ½ ∫ ω(β, β')`.
* `TauCeti.pathIntegral_radialPrimitive_stdComplexSymplecticForm_circleMap`: on `ℂ`,
  `∮_{|z - z₀| = r} (x dy - y dx) / 2 = π r²`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the radial Liouville vector field of a symplectic vector space).
-/

public section

open scoped Manifold Real

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The line integral of the radial primitive `λₓ(v) = ω(x, v) / 2` along a curve `β` in `V` is
half the integral of `ω(β, β')`. -/
theorem pathIntegral_radialPrimitive (β : ℝ → V) (a c : ℝ) :
    pathIntegral ω.radialPrimitive.val β a c = 2⁻¹ * ∫ t in a..c, ω (β t) (deriv β t) := by
  rw [pathIntegral_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hv : (fun _ : Fin 1 ↦ Manifold.curveVelocity 𝓘(ℝ, V) β t) = ![deriv β t] := by
    funext k
    fin_cases k
    exact Manifold.curveVelocity_eq_deriv
  simp only [hv]
  exact ω.radialPrimitive_apply (β t) (deriv β t)

end SymplecticForm

/-- **The boundary period of a disc in `ℂ`.** For the standard area form of `ℂ`, whose radial
primitive is `(x dy - y dx) / 2`, the line integral around the circle of radius `r` about `z₀` is
`π r²`, the area of the disc. -/
theorem pathIntegral_radialPrimitive_stdComplexSymplecticForm_circleMap (z₀ : ℂ) (r : ℝ) :
    pathIntegral stdComplexSymplecticForm.radialPrimitive.val (circleMap z₀ r) (-π) π =
      π * r ^ 2 := by
  -- The action of the radial primitive of the standard area form is the signed area.
  rw [SymplecticForm.pathIntegral_radialPrimitive]
  simp only [stdComplexSymplecticForm_apply]
  rw [inv_mul_eq_div, ← signedArea_def]
  have h := signedArea_circleMap z₀ r (-π)
  rwa [show -π + 2 * π = π by ring] at h

end TauCeti
