/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The area form of the plane as a smooth two-form

The standard symplectic form of `ℝ × ℝ` is the area form `dx ∧ dy`
(`TauCeti.stdSymplecticForm_real_apply`). This file evaluates the corresponding constant smooth
two-form `(stdSymplecticForm (V := ℝ)).constSmooth` on tangent vectors of the plane:
`(v, w) ↦ v₁ w₂ - v₂ w₁` (`TauCeti.eval₂_constSmooth_stdSymplecticForm`).
-/

public section

open scoped Manifold

namespace TauCeti

/-- The constant two-form `dx ∧ dy` on the plane evaluates as `(v, w) ↦ v₁ w₂ - v₂ w₁`. -/
theorem eval₂_constSmooth_stdSymplecticForm (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    (stdSymplecticForm (V := ℝ)).constSmooth.eval₂ x v w = v.1 * w.2 - v.2 * w.1 := by
  rw [SymplecticForm.fromTangentSpace_constSmooth_apply, stdSymplecticForm_real_apply,
    NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply]

end TauCeti
