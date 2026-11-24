/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Form

/-!
# The invariant Hermitian form on binary forms in small degree

Checks of `TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.Form` in two complex
variables `x = X 0` and `y = X 1`. Each value below excludes a plausible wrong convention.

* In degree `0` the unit has squared norm `1`; in degree `2` the monomial `x y` has squared norm
  `1 / 2`, where the unweighted coefficient form would give `1`, and `x²` and `x y` are
  orthogonal.
* The form is conjugate-linear in its first argument: pairing `i x` with `x` gives `-i`, and
  pairing `x` with `i x` gives `i`.
* The form of degree `1` vanishes on the nonzero constant `1`: positivity holds on the forms of
  degree `d` only.
-/

public section

open MvPolynomial Complex

namespace TauCeti.Examples

/-- In degree `0` the unit has squared norm `1`. -/
example : polynomialForm 0 (1 : MvPolynomial (Fin 2) ℂ) 1 = 1 := by
  simpa using polynomialForm_polynomialMonomial (𝕜 := ℂ) 0 0 0

/-- In degree `2` the monomial `x y` has squared norm `1 / choose 2 1 = 1 / 2`. -/
example : polynomialForm 2 (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) (X 0 * X 1) = 1 / 2 := by
  simpa [polynomialMonomial_of_le] using polynomialForm_polynomialMonomial (𝕜 := ℂ) 2 1 1

/-- In degree `2` the monomials `x²` and `x y` are orthogonal. -/
example : polynomialForm 2 (X 0 ^ 2 : MvPolynomial (Fin 2) ℂ) (X 0 * X 1) = 0 := by
  simpa [polynomialMonomial_of_le] using polynomialForm_polynomialMonomial (𝕜 := ℂ) 2 0 1

/-- The form is conjugate-linear in its first argument. -/
example : polynomialForm 1 (I • X 0 : MvPolynomial (Fin 2) ℂ) (X 0) = -I := by
  simp [X, smul_monomial, Finsupp.multinomial_eq]

/-- The form is linear in its second argument. -/
example : polynomialForm 1 (X 0 : MvPolynomial (Fin 2) ℂ) (I • X 0) = I := by
  simp [X, smul_monomial, Finsupp.multinomial_eq]

/-- The form of degree `1` vanishes on the nonzero constant `1`, which has degree `0`. -/
example : polynomialForm 1 (1 : MvPolynomial (Fin 2) ℂ) 1 = 0 := by
  simp [← C_1, ← monomial_zero']

end TauCeti.Examples
