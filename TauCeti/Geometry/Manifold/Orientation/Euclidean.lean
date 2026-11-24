/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The standard orientation of `ℝᵖ`

The standard orientation of `ℝᵖ = EuclideanSpace ℝ (Fin p)`
(`TauCeti.Manifold.Orientation.euclideanSpace p`) is the constant orientation in which the
standard basis `(e₁, …, eₚ)` is positive. It is the `ℝᵖ` analogue of
`TauCeti.Manifold.Orientation.real`.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

/-- The standard orientation of `ℝᵖ`, the constant orientation in which the standard basis
`(e₁, …, eₚ)` is positive. -/
def euclideanSpace (p : ℕ) :
    Orientation 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin p)) (Fin p) :=
  model (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.orientation (by simp)

/-- The standard orientation of `ℝᵖ` is the constant model orientation of the standard basis. -/
theorem euclideanSpace_eq_model (p : ℕ) :
    euclideanSpace p = model (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.orientation (by simp) :=
  (rfl)

/-- At every point of `ℝᵖ`, the standard orientation is the orientation of the standard basis. -/
@[simp]
theorem orientationAt_euclideanSpace (p : ℕ) (x : EuclideanSpace ℝ (Fin p)) :
    orientationAt (euclideanSpace p) x = (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.orientation :=
  orientationAt_model ..

end TauCeti.Manifold.Orientation
