/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Algebra.BigOperators.Fin

/-!
# Leading blocks of partial-correlation matrices

Restricting partial correlations to their first `q` rows and columns commutes with both the
triangular construction and its Gram matrix. Conversely, reading partial correlations from a
leading triangular block selects the same coordinates. These deterministic identities allow
principal-block laws of random correlation matrices to be calculated by projecting their
independent partial correlations.

The identities hold for arbitrary real coordinates, including the boundary and the totalized
square-root branches outside the correlation cube.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti

namespace strictLowerTriangle

/-- Include the strictly lower positions of a leading block into those of the full matrix. -/
def castLE {q p : ℕ} (h : q ≤ p) : strictLowerTriangle q ↪ strictLowerTriangle p :=
  ((Fin.castLEEmb h).prodMap (Fin.castLEEmb h)).subtypeMap fun _ hji ↦ hji

/-- The position embedding casts each of its two indices. -/
@[simp]
theorem castLE_apply {q p : ℕ} (h : q ≤ p) (ij : strictLowerTriangle q) :
    castLE h ij = ⟨(ij.1.1.castLE h, ij.1.2.castLE h), ij.2⟩ := (rfl)

end strictLowerTriangle

variable {p q : ℕ}

/-- Taking a leading principal block commutes with the partial-correlation triangular
construction, without any restriction on the coordinates. -/
@[simp]
theorem partialCorrelationCholesky_submatrix_castLE (h : q ≤ p)
    (z : strictLowerTriangle p → ℝ) :
    (partialCorrelationCholesky z).submatrix (Fin.castLE h) (Fin.castLE h) =
      partialCorrelationCholesky (z ∘ strictLowerTriangle.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, partialCorrelationCholesky_apply]
  rw [Fin.prod_Iio_castLE]
  simp

/-- Taking a leading principal block commutes with the partial-correlation Gram construction.
In particular, the block depends only on partial correlations whose two indices lie in it. -/
@[simp]
theorem partialCorrelationGram_submatrix_castLE (h : q ≤ p)
    (z : strictLowerTriangle p → ℝ) :
    (partialCorrelationGram z).submatrix (Fin.castLE h) (Fin.castLE h) =
      partialCorrelationGram (z ∘ strictLowerTriangle.castLE h) := by
  rw [partialCorrelationGram_def,
    (isLowerTriangular_partialCorrelationCholesky z).submatrix_castLE_mul_transpose h,
    partialCorrelationCholesky_submatrix_castLE, partialCorrelationGram_def]

/-- Reading partial correlations from a leading principal block selects the corresponding
partial correlations of the original matrix. No triangularity or positivity is needed. -/
@[simp]
theorem _root_.Matrix.partialCorrelationOfCholesky_submatrix_castLE (h : q ≤ p)
    (L : Matrix (Fin p) (Fin p) ℝ) :
    (L.submatrix (Fin.castLE h) (Fin.castLE h)).partialCorrelationOfCholesky =
      L.partialCorrelationOfCholesky ∘ strictLowerTriangle.castLE h := by
  funext ij
  simp only [Matrix.partialCorrelationOfCholesky_apply, Matrix.submatrix_apply,
    Function.comp_apply, strictLowerTriangle.castLE_apply, Fin.sum_Iio_castLE]

end TauCeti
