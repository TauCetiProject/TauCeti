/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Bivariate specialization

In the bivariate polynomial ring `R[X][Y]`, a coefficient homomorphism `evalRingHom b : R[X] →+* R`
evaluates the inner variable `X` at `b`, yielding the univariate fiber `P(b, Y)`. Over a
nontrivial commutative ring, this inner-variable specialization of any primitive bivariate
polynomial `F : R[X][Y]` is nonzero for every `b : R`
(`Polynomial.IsPrimitive.map_evalRingHom_ne_zero`).

## Main results

* `Polynomial.IsPrimitive.map_evalRingHom_ne_zero`: over a nontrivial commutative ring,
  specializing the inner variable `X` of a primitive bivariate polynomial `F : R[X][Y]` at any
  `b : R` yields a nonzero polynomial `F(b, Y)`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Over a nontrivial commutative ring, specializing the inner variable `X` (i.e. evaluating the
coefficient polynomials in `R[X]`) of a primitive bivariate polynomial `F : R[X][Y]` at any scalar
`b : R` yields a nonzero univariate polynomial `F(b, Y)` (unlike specializing the outer variable
`Y`, which can vanish). -/
theorem IsPrimitive.map_evalRingHom_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {F : R[X][Y]} (hF : F.IsPrimitive) (b : R) :
    F.map (evalRingHom b) ≠ 0 := by
  intro h0
  have hdvd : C (X - C b) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot, IsRoot]
    have hi : (F.map (evalRingHom b)).coeff i = 0 := by rw [h0, coeff_zero]
    simpa [coeff_map] using hi
  exact not_isUnit_X_sub_C b (hF _ hdvd)

end Polynomial
