/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree bounds for determinants of polynomial matrices

If every entry in the `j`-th column of a square matrix `A` with entries in `R[X]` has natural
degree at most `e j`, then every term in the Leibniz expansion of `A.det` has natural degree at
most `∑ j, e j`, and hence `A.det.natDegree ≤ ∑ j, e j`.

## Main results

* `Matrix.natDegree_det_le_of_natDegree_le`: natural-degree bound for the determinant of a
  polynomial matrix from columnwise degree bounds.
-/

public section

namespace Matrix

open Polynomial

/-- If the `j`-th column of a polynomial matrix `A` has degree at most `e j`, then `det A` has
degree at most `∑ j, e j`. -/
theorem natDegree_det_le_of_natDegree_le {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R[X]) (e : n → ℕ) (h : ∀ i j, (A i j).natDegree ≤ e j) :
    A.det.natDegree ≤ ∑ j, e j := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ ↦ h (σ j) j)

end Matrix
