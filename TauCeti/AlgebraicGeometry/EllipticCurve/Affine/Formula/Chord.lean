/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Chord identities on a Weierstrass curve

For two points `(x₁, y₁)` and `(x₂, y₂)` on a Weierstrass curve `W`, subtracting the two equations
of `W` factors `y₁ - y₂` against `x₁ - x₂`. This file records the two resulting identities, one
for each choice of the second factor of `y₁ - y₂`. They say how fast `y₁ - y₂` vanishes as
`x₁ - x₂` does, which is what the slope of the chord through the two points measures.

## Main results

* `WeierstrassCurve.Affine.Y_sub_Y_mul_Y_add_Y_eq`:
  `(y₁ - y₂) (y₁ + y₂ + a₁ x₁ + a₃) = (x₁ - x₂) (x₁² + x₁ x₂ + x₂² + a₂ (x₁ + x₂) + a₄ - a₁ y₂)`.
* `WeierstrassCurve.Affine.Y_sub_Y_mul_Y_sub_negY_eq`:
  `(y₁ - y₂) (y₁ - negY x₂ y₂) = (x₁ - x₂) (x₁² + x₁ x₂ + x₂² + a₂ (x₁ + x₂) + a₄ - a₁ y₁)`,
  whose `x₁ = x₂` case over a field is Mathlib's `Y_eq_of_X_eq`: the two points over `x₂` are
  `(x₂, y₂)` and its negative.
-/

public section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W : Affine R} {x₁ y₁ x₂ y₂ : R}

/-- The chord identity with second factor `y₁ + y₂ + a₁ x₁ + a₃`. -/
theorem Y_sub_Y_mul_Y_add_Y_eq (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
  rw [equation_iff] at h₁ h₂
  linear_combination h₁ - h₂

/-- The chord identity with second factor `y₁ - negY x₂ y₂`. Over a field, its case `x₁ = x₂` says
that the only points over `x₂` are `(x₂, y₂)` and `-(x₂, y₂)`. -/
theorem Y_sub_Y_mul_Y_sub_negY_eq (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ - W.negY x₂ y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) := by
  rw [equation_iff] at h₁ h₂
  rw [negY]
  linear_combination h₁ - h₂

end WeierstrassCurve.Affine
