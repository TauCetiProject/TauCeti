/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Partial degrees of determinants of multivariate polynomials

Let `A` be a square matrix with entries in `MvPolynomial σ R` whose `l`-th column has partial
degree at most `e l` in the variable `Xᵢ`. Every term of the Leibniz expansion of `det A` is, up
to sign, a product containing exactly one entry from each column, so `det A` has partial degree
at most `∑ l, e l` in `Xᵢ`.

## Main results

* `Matrix.degreeOf_det_le_sum`: the partial degree of a determinant is bounded by
  the sum of the column-wise partial-degree bounds.
-/

public section

namespace Matrix

open MvPolynomial Finset

variable {R σ n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- If the `l`-th column of a matrix `A` of multivariate polynomials has partial degree at most
`e l` in `Xᵢ`, then `det A` has partial degree at most `∑ l, e l` in `Xᵢ`. -/
theorem degreeOf_det_le_sum (A : Matrix n n (MvPolynomial σ R)) (i : σ) (e : n → ℕ)
    (hA : ∀ k l, (A k l).degreeOf i ≤ e l) :
    A.det.degreeOf i ≤ ∑ l, e l := by
  rw [det_apply]
  refine (degreeOf_sum_le i univ _).trans (Finset.sup_le fun p _ ↦ ?_)
  calc
    (Equiv.Perm.sign p • ∏ l, A (p l) l).degreeOf i =
        (∏ l, A (p l) l).degreeOf i := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      · rw [hp, one_smul]
      · rw [hp, Units.neg_smul, one_smul, degreeOf_neg]
    _ ≤ ∑ l, (A (p l) l).degreeOf i := degreeOf_prod_le i univ _
    _ ≤ ∑ l, e l := Finset.sum_le_sum fun l _ ↦ hA (p l) l

end Matrix
