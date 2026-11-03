/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Constant units of Laurent polynomials

A constant Laurent polynomial `C r` is a unit exactly when its coefficient `r` is a unit. The map
`C` is Mathlib's `AddMonoidAlgebra.singleZeroRingHom`, which is a local ring homomorphism. This is
the Laurent counterpart of Mathlib's `Polynomial.isUnit_C`.

## Main results

* `LaurentPolynomial.isUnit_C`: `C r` is a unit if and only if `r` is.
-/

public section

namespace LaurentPolynomial

variable {R : Type*} [Semiring R]

/-- A constant Laurent polynomial is a unit exactly when its coefficient is. -/
@[simp]
theorem isUnit_C {r : R} : IsUnit (C r : R[T;T⁻¹]) ↔ IsUnit r :=
  isUnit_map_iff (AddMonoidAlgebra.singleZeroRingHom (R := R) (M := ℤ)) r

end LaurentPolynomial
