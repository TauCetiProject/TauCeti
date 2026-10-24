/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
import TauCeti.Algebra.Polynomial.BigOperators

/-!
# The top coefficient of a determinant of polynomials

Let `A` be a square matrix with polynomial entries whose `j`-th column has degree at most `e j`.
Every term of the Leibniz expansion of `det A` then has degree at most `∑ j, e j`, so `det A` does
too, and its coefficient in that degree is the determinant of the scalar matrix of
top coefficients `(A i j).coeff (e j)`. This is the standard way to show that a determinant of
polynomials is nonzero, by exhibiting a nonsingular matrix of leading coefficients.
-/

public section

namespace Matrix

open Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then the coefficient
of `det A` in degree `∑ j, e j` is the determinant of the matrix of coefficients of the entries
in the degrees `e j`. -/
theorem coeff_det_sum_eq_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.coeff (∑ j, e j) = (of fun i j ↦ (A i j).coeff (e j)).det := by
  simp only [det_apply', finsetSum_coeff, coeff_intCast_mul, of_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [coeff_prod_sum_eq_of_natDegree_le _ _ _ fun j _ ↦ h (σ j) j]

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then `det A` has
degree at most `∑ j, e j`. -/
theorem natDegree_det_le_of_natDegree_le (A : Matrix n n R[X]) (e : n → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.natDegree ≤ ∑ j, e j := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ ↦ h (σ j) j)

end Matrix
