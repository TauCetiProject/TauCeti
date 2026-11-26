/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Rectangular
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Permutation unitaries for C⋆-matrices

Transports `Matrix.permutationUnitary` along `CStarMatrix.ofMatrixRingEquiv` to define
`CStarMatrix.permutationUnitary`, together with its coercion formula and reindexing identity.

## Main declarations

* `CStarMatrix.permutationUnitary`: the group homomorphism
  `Equiv.Perm n →* unitary (CStarMatrix n n A)`.
* `CStarMatrix.coe_permutationUnitary`: coercion of `permutationUnitary σ` to `CStarMatrix n n A`.
* `CStarMatrix.permutationUnitary_conj`: conjugation by `permutationUnitary σ` agrees with
  `CStarMatrix.reindexₐ R A σ`.
-/

public section

open Matrix

namespace CStarMatrix

variable {n R A : Type*} [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]

/-- Permutation unitaries form a group homomorphism
`Equiv.Perm n →* unitary (CStarMatrix n n A)`, transporting `Matrix.permutationUnitary` along
`ofMatrixRingEquiv`. -/
def permutationUnitary : Equiv.Perm n →* unitary (CStarMatrix n n A) :=
  (Unitary.map (⟨(ofMatrixRingEquiv : Matrix n n A ≃+* CStarMatrix n n A).toMonoidHom,
    fun _ => rfl⟩ : Matrix n n A →⋆* CStarMatrix n n A)).toMonoidHom.comp
    Matrix.permutationUnitary

/-- The underlying matrix of `permutationUnitary σ` is `ofMatrix (σ⁻¹.permMatrix A)`. -/
@[simp]
theorem coe_permutationUnitary (σ : Equiv.Perm n) :
    (permutationUnitary (A := A) σ : CStarMatrix n n A) = ofMatrix (σ⁻¹.permMatrix A) :=
  congrArg ofMatrix (Matrix.coe_permutationUnitary σ)

/-- Conjugation by `permutationUnitary σ` agrees with `reindexₐ R A σ`. -/
theorem permutationUnitary_conj [Semiring R] [Module R A] (σ : Equiv.Perm n)
    (M : CStarMatrix n n A) :
    (permutationUnitary (A := A) σ : CStarMatrix n n A) * M *
        star (permutationUnitary (A := A) σ : CStarMatrix n n A) = reindexₐ R A σ M := by
  ext i j
  simp only [coe_permutationUnitary, star_eq_conjTranspose, ← ofMatrix_conjTranspose,
    Matrix.conjTranspose_permMatrix, inv_inv, reindexₐ_apply]
  calc (ofMatrix (σ⁻¹.permMatrix A) * M * ofMatrix (σ.permMatrix A)) i j
      = (ofMatrix.symm (ofMatrix (σ⁻¹.permMatrix A) * M * ofMatrix (σ.permMatrix A))) i j := by
        rw [ofMatrix_symm_apply]
    _ = ((σ⁻¹.permMatrix A * ofMatrix.symm M) * σ.permMatrix A) i j := by
        simp only [ofMatrix_symm_mul, Equiv.symm_apply_apply]
    _ = M (σ.symm i) (σ.symm j) := by
        rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
          PEquiv.mul_toMatrix_toPEquiv]
        simp [ofMatrix_symm_apply]

end CStarMatrix
