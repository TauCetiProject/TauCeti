/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity

/-!
# Unitary equivalence of matrix Gram factors

Two rectangular matrices with the same row index type have equal column Gram matrices exactly
when one is obtained from the other by left multiplication by a unitary matrix. No rank or
nondegeneracy assumption is required: the unitary extends the isometry between the column
spans and need not be unique on their orthogonal complements.

This identifies the ambiguity in a positive-semidefinite Gram factorization, including
zero-padded factorizations. The proof uses `TauCeti.gram_eq_iff_exists_linearIsometryEquiv`
and Mathlib's `LinearIsometryEquiv.toMatrix_mem_unitaryGroup` to pass from Gram rigidity
of column families to the matrix statement.

For the matrix Gram-factorization interpretation, see Horn and Johnson, *Matrix Analysis*,
2nd ed., §7.2.
-/

public section

noncomputable section

namespace TauCeti

open Matrix
open scoped InnerProductSpace

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m]

/-- Two matrices with the same row index type have equal column Gram matrices if and only
if they differ by left multiplication by a unitary matrix. The column index type may be
infinite, and the columns need not span the row space. -/
theorem conjTranspose_mul_self_eq_iff_exists_unitary_mul {A B : Matrix m n 𝕜} :
    Aᴴ * A = Bᴴ * B ↔ ∃ U : Matrix.unitaryGroup m 𝕜, B = (U : Matrix m m 𝕜) * A := by
  constructor
  · intro h
    let a : n → EuclideanSpace 𝕜 m := fun j => WithLp.toLp 2 (fun i => A i j)
    let b : n → EuclideanSpace 𝕜 m := fun j => WithLp.toLp 2 (fun i => B i j)
    have hgram : Matrix.gram 𝕜 a = Matrix.gram 𝕜 b := by
      simpa [a, b, EuclideanSpace.basisFun_repr] using
        (Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun m 𝕜) a).trans
          (h.trans (Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun m 𝕜) b).symm)
    obtain ⟨e, he⟩ := gram_eq_iff_exists_linearIsometryEquiv.mp hgram
    let c := (EuclideanSpace.basisFun m 𝕜).toBasis
    refine ⟨⟨e.toMatrix c c, e.toMatrix_mem_unitaryGroup _ _⟩, ?_⟩
    ext i j
    have hj := LinearMap.toMatrix_mulVec_repr c c e.toLinearMap (a j)
    have := congrArg (fun x => x i) hj
    simpa [c, a, b, he j, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this.symm
  · rintro ⟨U, rfl⟩
    have hU : (U : Matrix m m 𝕜)ᴴ * (U : Matrix m m 𝕜) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp U.property
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (U : Matrix m m 𝕜), hU]

end TauCeti
