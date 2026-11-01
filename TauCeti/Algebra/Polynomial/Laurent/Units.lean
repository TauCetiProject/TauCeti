/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Constant units of Laurent polynomials

A constant Laurent polynomial `C r` is a unit exactly when its coefficient `r` is a unit. Evaluation
at `T = 1` is a ring map retracting `C`, so it carries an inverse of `C r` to an inverse of `r`.
This is the Laurent counterpart of Mathlib's `Polynomial.isUnit_C`.

## Main results

* `LaurentPolynomial.isUnit_C`: `C r` is a unit if and only if `r` is.
-/

public section

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

/-- A constant Laurent polynomial is a unit exactly when its coefficient is. -/
theorem isUnit_C {r : R} : IsUnit (C r : R[T;T⁻¹]) ↔ IsUnit r :=
  ⟨fun h ↦ by simpa using h.map (eval₂ (RingHom.id R) 1), fun h ↦ h.map C⟩

end LaurentPolynomial
