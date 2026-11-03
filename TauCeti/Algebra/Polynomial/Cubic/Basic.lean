/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant

/-!
# Elementary symmetric functions of the roots of a split cubic

A product `(X - a)(X - b)(X - c)` of three monic linear factors determines the elementary
symmetric functions of `a, b, c`: by Vieta's formulas they are, up to sign, its coefficients.
This file records the resulting comparison of two such factorisations over any commutative ring,
using Mathlib's expansion `Cubic.prod_X_sub_C_eq`.

## Main results

* `TauCeti.Polynomial.add_add_eq_and_mul_add_mul_add_mul_eq`: if
  `(X - a)(X - b)(X - c) = (X - a')(X - b')(X - c')`, then `a + b + c = a' + b' + c'` and
  `ab + ac + bc = a'b' + a'c' + b'c'`.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [CommRing R]

/-- Equal products of three monic linear factors have the same first and second elementary
symmetric functions of their roots. -/
theorem add_add_eq_and_mul_add_mul_add_mul_eq {a b c a' b' c' : R}
    (h : (X - C a) * (X - C b) * (X - C c) = (X - C a') * (X - C b') * (X - C c')) :
    a + b + c = a' + b' + c' ∧ a * b + a * c + b * c = a' * b' + a' * c' + b' * c' := by
  rw [Cubic.prod_X_sub_C_eq, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at h
  simp only [Cubic.mk.injEq, true_and, neg_inj] at h
  exact ⟨h.1, h.2.1⟩

end TauCeti.Polynomial
