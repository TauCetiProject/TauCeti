/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Simp lemmas for multivariate polynomial quotients

Companion `@[simp]` lemmas for `MvPolynomial.quotientEquivQuotientMvPolynomial`, evaluating both
directions on quotient classes and coefficientwise reductions over any variable type `σ`.

## Main results

* `MvPolynomial.quotientEquivQuotientMvPolynomial_symm_mk` and
  `MvPolynomial.quotientEquivQuotientMvPolynomial_map_mk`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {I : Ideal R}

/-- `quotientEquivQuotientMvPolynomial I` sends `p.map (mk I)` to `mk (I.map C) p`. -/
@[simp] theorem quotientEquivQuotientMvPolynomial_map_mk (p : MvPolynomial σ R) :
    quotientEquivQuotientMvPolynomial I (p.map (Ideal.Quotient.mk I)) =
      Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [quotientEquivQuotientMvPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [quotientEquivQuotientMvPolynomial]

/-- `(quotientEquivQuotientMvPolynomial I).symm` sends `mk (I.map C) p` to `p.map (mk I)`. -/
@[simp] theorem quotientEquivQuotientMvPolynomial_symm_mk (p : MvPolynomial σ R) :
    (quotientEquivQuotientMvPolynomial I).symm
        (Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ R)) p) =
      p.map (Ideal.Quotient.mk I) := by
  rw [AlgEquiv.symm_apply_eq, quotientEquivQuotientMvPolynomial_map_mk]

end MvPolynomial
