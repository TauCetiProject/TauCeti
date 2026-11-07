/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Star.Module

/-!
# Quaternion conjugation as a star module structure

Quaternion conjugation is linear over the base ring, when that ring has trivial star, by
`QuaternionAlgebra.star_smul`. This file records that fact as a `StarModule` instance, so that
the generic star API applies to quaternions: for instance the continuous linear equivalence
`starL'` and the derivative formula `HasFDerivAt.star_star` over the reals.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] [Star R] [TrivialStar R] {c₁ c₂ c₃ : R}

/-- Conjugation of a quaternion algebra is linear over a base ring with trivial star. -/
instance instStarModule : StarModule R ℍ[R,c₁,c₂,c₃] where
  star_smul r a := by rw [star_smul, star_trivial r]

end QuaternionAlgebra
