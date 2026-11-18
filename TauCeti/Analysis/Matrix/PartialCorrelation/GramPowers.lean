/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import TauCeti.LinearAlgebra.Matrix.Triangular.GramMonomial

/-!
# Powers of partial-correlation Gram entries

A monomial in entries of the partial-correlation Gram matrix expands into a finite sum of
monomials in entries of its lower-triangular Cholesky factor, for arbitrary partial correlations
`z`. This reduces mixed moments of the Gram entries, such as the mixed entry moments of the LKJ
law, to moments of Cholesky monomials. The expansion is the general lower-triangular one,
`Matrix.IsLowerTriangular.prod_mul_transpose_apply_pow_eq_sum`, applied to
`partialCorrelationCholesky z`.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {p : ℕ}

/-- A monomial in partial-correlation Gram entries is the finite sum of the Cholesky monomials
obtained by choosing a column `k ≤ min i j` for each occurrence of each Gram entry `(i, j)`. -/
theorem prod_pow_partialCorrelationGram_eq_sum
    (z : strictLowerTriangle p → ℝ) (n : Fin p × Fin p → ℕ) :
    (∏ ij, partialCorrelationGram z ij.1 ij.2 ^ n ij) =
      ∑ c : mulTransposeExpansionChoice n,
        ∏ q, partialCorrelationCholesky z q.1 q.2 ^ mulTransposeExpansionPower c q := by
  rw [partialCorrelationGram_def]
  exact (isLowerTriangular_partialCorrelationCholesky z).prod_mul_transpose_apply_pow_eq_sum n

end TauCeti
