/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Rectangular
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Permutation

/-!
# Permutation unitaries for C⋆-matrices

Relates conjugation by `CStarMatrix.ofMatrix (Matrix.permutationUnitary σ : Matrix n n A)` to
`CStarMatrix.reindexₐ R A σ`.

## Main declarations

* `CStarMatrix.ofMatrix_permutationUnitary_conj`: conjugation by
  `ofMatrix (Matrix.permutationUnitary σ : Matrix n n A)` agrees with `CStarMatrix.reindexₐ R A σ`.
-/

public section

open Matrix

namespace CStarMatrix

variable {n R A : Type*} [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]

/-- Conjugation by `ofMatrix (Matrix.permutationUnitary σ : Matrix n n A)` agrees with
`reindexₐ R A σ`. -/
theorem ofMatrix_permutationUnitary_conj [Semiring R] [Module R A] (σ : Equiv.Perm n)
    (M : CStarMatrix n n A) :
    ofMatrix (Matrix.permutationUnitary (R := A) σ : Matrix n n A) * M *
        star (ofMatrix (Matrix.permutationUnitary (R := A) σ : Matrix n n A)) =
      reindexₐ R A σ M := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, ofMatrix_symm_star, Equiv.symm_apply_apply, ofMatrix_symm_reindexₐ]
  rw [Matrix.coe_permutationUnitary, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrixHom_apply (R := A) σ, ← Matrix.permMatrixHom_apply (R := A) σ⁻¹,
    Matrix.permMatrixHom_mul, Matrix.mul_permMatrixHom]
  rfl

end CStarMatrix
