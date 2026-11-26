/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.Determinant

import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.Matrix.GramFactorization

/-!
# Bounds on Gram determinants

Hadamard's inequality bounds the determinant norm of a positive semidefinite matrix by the
product of the norms of its diagonal entries. Fischer's inequality bounds the Gram determinant
of a concatenated family by the product of the two individual Gram determinants. Both bounds
include singular and empty matrices.
-/

public section

open scoped ComplexOrder

namespace Matrix

/-- The determinant norm of a positive semidefinite matrix is at most the product of the
norms of its diagonal entries. -/
theorem PosSemidef.norm_det_le_prod_norm_diag {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) : ‖A.det‖ ≤ ∏ i, ‖A i i‖ := by
  obtain ⟨X, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hA
  let v : n → EuclideanSpace 𝕜 n := fun j ↦ WithLp.toLp 2 (fun i ↦ X i j)
  have hv : gram 𝕜 v = Xᴴ * X := by
    rw [gram_eq_conjTranspose_mul (EuclideanSpace.basisFun n 𝕜) v]
    simp [v, EuclideanSpace.basisFun_repr]
    rfl
  rw [← hv, ← RCLike.ofReal_le_ofReal (K := 𝕜),
    RCLike.norm_of_nonneg' (posSemidef_gram 𝕜 v).det_nonneg]
  simpa [map_prod, gram_apply, inner_self_eq_norm_sq_to_K] using det_gram_le_prod_norm_sq (𝕜 := 𝕜) v

/-- The Gram determinant norm of concatenated columns is at most the product of the two Gram
determinant norms, for a positive semidefinite form `G`. -/
theorem PosSemidef.norm_det_fromCols_gram_le {𝕜 m n p : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] {G : Matrix m m 𝕜}
    (hG : G.PosSemidef) (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    ‖((fromCols A B)ᴴ * G * fromCols A B).det‖ ≤
      ‖(Aᴴ * G * A).det‖ * ‖(Bᴴ * G * B).det‖ := by
  have hAB := hG.conjTranspose_mul_mul_same (fromCols A B)
  have hblock : (fromCols A B)ᴴ * G * fromCols A B =
      fromBlocks (Aᴴ * G * A) (Aᴴ * G * B) (Aᴴ * G * B)ᴴ (Bᴴ * G * B) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hG.isHermitian.eq, Matrix.mul_assoc]
  have h := (hblock ▸ hAB).det_fromBlocks_le
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜), RCLike.ofReal_mul,
    RCLike.norm_of_nonneg' hAB.det_nonneg,
    RCLike.norm_of_nonneg' (hG.conjTranspose_mul_mul_same A).det_nonneg,
    RCLike.norm_of_nonneg' (hG.conjTranspose_mul_mul_same B).det_nonneg]
  exact hblock.symm ▸ h

end Matrix
