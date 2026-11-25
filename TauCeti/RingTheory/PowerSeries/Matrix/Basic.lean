/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficient matrices of matrices of power series

A matrix `M` over `R⟦X⟧` is determined by its coefficient matrices `M.map (coeff k)`, and those of
a product are given by the Cauchy product. Matrix equations over `R⟦X⟧` can therefore be solved
coefficient by coefficient; these two facts are the common setup for such recursions.

## Main results

* `PowerSeries.matrix_ext`: two matrices of power series with the same coefficient matrices are
  equal.
* `PowerSeries.map_coeff_matrix_mul`: the coefficients of a product of matrices of power series.
-/

public section

namespace PowerSeries

open Finset Matrix

variable {R : Type*} {l m n : Type*} [Semiring R]

/-- Two matrices of power series are equal if all their coefficient matrices are. -/
theorem matrix_ext {M N : Matrix m n R⟦X⟧} (h : ∀ k, M.map (coeff k) = N.map (coeff k)) :
    M = N := by
  ext i j k
  exact congrFun (congrFun (h k) i) j

/-- The `k`-th coefficient matrix of a product of matrices of power series is the Cauchy product
`∑_{i + j = k} Mᵢ Nⱼ` of the coefficient matrices. -/
theorem map_coeff_matrix_mul [Fintype m] (M : Matrix l m R⟦X⟧) (N : Matrix m n R⟦X⟧) (k : ℕ) :
    (M * N).map (coeff k) = ∑ p ∈ antidiagonal k, M.map (coeff p.1) * N.map (coeff p.2) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, coeff_mul, Matrix.sum_apply]
  exact Finset.sum_comm

end PowerSeries
