/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# The addition polynomial of a line

For a Weierstrass curve `W` and a line `y = ℓ x + ν` through `(x₁, y₁)`, Mathlib's addition
polynomial `W.addPolynomial x₁ y₁ ℓ` is the Weierstrass polynomial restricted to the line,
`W(X, ℓ X + ν)`. This file records that substitution in terms of the line's intercept, and the
coefficients of `X²` and `X` it forces when it factors as `-(X - x₁) (X - x₂) (X - x₃)`.

## Main results

* `WeierstrassCurve.Affine.addPolynomial_eq_eval`: if `y₁ = ℓ x₁ + ν`, then
  `W.addPolynomial x₁ y₁ ℓ = W(X, ℓ X + ν)`.
* `WeierstrassCurve.Affine.coeffs_of_addPolynomial_eq`: a factorisation
  `W.addPolynomial x₁ y₁ ℓ = -(X - x₁) (X - x₂) (X - x₃)` determines `x₁ + x₂ + x₃` and
  `x₁ x₂ + x₁ x₃ + x₂ x₃` from `ℓ`, `x₁`, `y₁` and the coefficients of `W`.
-/

public section

namespace WeierstrassCurve.Affine

open Polynomial

variable {R : Type*} [CommRing R] {W : Affine R} {x₁ x₂ x₃ y₁ ℓ ν : R}

/-- Substituting the line `y = ℓ x + ν` through `(x₁, y₁)` into the Weierstrass polynomial gives
the addition polynomial of `(x₁, y₁)` with slope `ℓ`. -/
theorem addPolynomial_eq_eval (hy₁ : y₁ = ℓ * x₁ + ν) :
    W.addPolynomial x₁ y₁ ℓ = W.polynomial.eval (C ℓ * X + C ν) := by
  rw [addPolynomial, linePolynomial, hy₁, C_add, C_mul]
  congr 1
  ring

/-- Comparing the coefficients of `X²` and `X` in a factorisation of the addition polynomial. -/
theorem coeffs_of_addPolynomial_eq
    (h : W.addPolynomial x₁ y₁ ℓ = -((X - C x₁) * (X - C x₂) * (X - C x₃))) :
    ℓ ^ 2 + W.a₁ * ℓ - W.a₂ = x₁ + x₂ + x₃ ∧
      2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
        x₁ * x₂ + x₁ * x₃ + x₂ * x₃ := by
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj] at h
  have h' := (Cubic.toPoly_injective _ _).1 h
  exact ⟨by linear_combination -congrArg Cubic.b h', congrArg Cubic.c h'⟩

end WeierstrassCurve.Affine
