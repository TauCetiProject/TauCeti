/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Partial degrees of the image of a polynomial under a coefficient map

A ring homomorphism `f : R →+* S` applied to the coefficients of a multivariate polynomial `P`
can only remove monomials, so it does not raise any partial degree. This is the partial-degree
form of Mathlib's `MvPolynomial.degrees_map_le`.

## Main results

* `MvPolynomial.degreeOf_map_le`: `degreeOf i (P.map f) ≤ degreeOf i P`.
-/

public section

namespace MvPolynomial

/-- Mapping the coefficients of `P` does not raise its degree in `Xᵢ`. -/
theorem degreeOf_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial σ R) (i : σ) : (P.map f).degreeOf i ≤ P.degreeOf i :=
  degreeOf_le_iff.2 fun _ hs ↦ monomial_le_degreeOf i (support_map_subset f P hs)

end MvPolynomial
