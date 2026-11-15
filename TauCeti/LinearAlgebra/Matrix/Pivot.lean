/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A symmetric matrix pivot for Gaussian elimination

Let `A` and `C` be two square matrices over a field. If their kernels meet trivially and
`Aᵀ C = Cᵀ A`, then some symmetric matrix `X` makes `A + X C` invertible. Applied to the
left blocks of a symplectic matrix, this says that multiplication by an upper symplectic
unipotent can make the upper-left block invertible. This is the pivot step in the Gaussian
decomposition of the symplectic group.

## Main result

* `TauCeti.exists_isSymm_isUnit_add_mul_of_ker_inter_eq_bot_of_transpose_mul_comm` constructs the
  symmetric pivot.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Chapter II, §1.

The statement and the reduction of `C` to rank normal form are adapted from Mathlib's private lemma
`Matrix.SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` in
`Mathlib.LinearAlgebra.SymplecticGroup` (Apache-2.0). It is made public here because symplectic
Gaussian generation needs the constructed symmetric pivot, while Mathlib uses it only internally
to prove that symplectic matrices have determinant one. In normal form `C` is a symmetric
idempotent `P`, and the pivot `P - P Q` is written without block decompositions.
-/

public section

open Matrix

namespace TauCeti

/-- The normal-form case of the pivot: if `P` is a symmetric idempotent, `Qᵀ P = Pᵀ Q`, and
the only vector annihilated by both `Q` and `P` is zero, then some symmetric matrix `Y` (namely
`P - P Q`) makes `Q + Y P` invertible. -/
private theorem exists_isSymm_isUnit_add_mul_of_isIdempotentElem {K : Type*} [Field K]
    {l : Type*} [Fintype l] [DecidableEq l] {P Q : Matrix l l K} (hPsymm : P.IsSymm)
    (hPP : IsIdempotentElem P) (hker : ∀ x : l → K, Q *ᵥ x = 0 → P *ᵥ x = 0 → x = 0)
    (hcomm : Qᵀ * P = Pᵀ * Q) :
    ∃ Y : Matrix l l K, Y.IsSymm ∧ IsUnit (Q + Y * P) := by
  rw [hPsymm.eq] at hcomm
  have hYP : (P - P * Q) * P = P - P * Q := by
    rw [sub_mul, hPP.eq, ← hcomm, mul_assoc, hPP.eq]
  refine ⟨P - P * Q, ?_, ?_⟩
  · rw [IsSymm, transpose_sub, transpose_mul, hPsymm.eq, hcomm]
  -- `Q + (P - P Q) P` kills only vectors killed by both `Q` and `P`.
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot,
    ker_mulVecLin_eq_bot_iff]
  intro x hx
  have hPx : P *ᵥ x = 0 := by
    have hPM : P * (Q + (P - P * Q) * P) = P := by
      rw [hYP, mul_add, mul_sub, ← mul_assoc, hPP.eq, add_sub_cancel]
    rw [← hPM, ← mulVec_mulVec, hx, mulVec_zero]
  refine hker x ?_ hPx
  rwa [add_mulVec, ← mulVec_mulVec, hPx, mulVec_zero, add_zero] at hx

/-- Given square matrices `A` and `C` over a field, if the only vector annihilated by both is
zero and `Aᵀ C = Cᵀ A`, then a symmetric left multiplier makes `A + X C` invertible. -/
theorem exists_isSymm_isUnit_add_mul_of_ker_inter_eq_bot_of_transpose_mul_comm
    {K : Type*} [Field K] {l : Type*} [Fintype l] [DecidableEq l]
    {A C : Matrix l l K}
    (hker : ∀ x : l → K, A *ᵥ x = 0 → C *ᵥ x = 0 → x = 0)
    (hcomm : Aᵀ * C = Cᵀ * A) :
    ∃ X : Matrix l l K, X.IsSymm ∧ IsUnit (A + X * C) := by
  -- Put `C` into rank normal form `V C U`, a symmetric idempotent, and transport `A` to
  -- `Vᵀ⁻¹ A U` by the matching basis changes.
  obtain ⟨V, U, s, hV, hU, hP⟩ := exists_rank_normal_form C
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  obtain ⟨Y, hY, hunit⟩ :=
    exists_isSymm_isUnit_add_mul_of_isIdempotentElem (P := V * C * U) (Q := Vᵀ⁻¹ * A * U)
      (by rw [hP, IsSymm, transpose_submatrix, fromBlocks_transpose]; simp)
      (by rw [IsIdempotentElem, hP, submatrix_mul_equiv, fromBlocks_multiply]; simp)
      (fun x hQx hPx ↦ by
        have hUx : U *ᵥ x = 0 := hker _
          (by simpa [mulVec_mulVec, mul_assoc] using congrArg (Vᵀ *ᵥ ·) hQx)
          (by simpa [mulVec_mulVec, mul_assoc] using congrArg (V⁻¹ *ᵥ ·) hPx)
        simpa [mulVec_mulVec] using congrArg (U⁻¹ *ᵥ ·) hUx)
      (by
        simp only [mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose,
          inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
        rw [← mul_assoc Aᵀ, hcomm, mul_assoc])
  -- Conjugating `Y` back through `V` gives the required symmetric matrix.
  refine ⟨Vᵀ * Y * V, by simp [IsSymm, transpose_mul, hY.eq, mul_assoc], ?_⟩
  have : A + Vᵀ * Y * V * C = Vᵀ * (Vᵀ⁻¹ * A * U + Y * (V * C * U)) * U⁻¹ := by
    simp only [mul_add, add_mul, mul_assoc, mul_inv_cancel_left_of_invertible,
      mul_inv_of_invertible, mul_one]
  rw [this]
  exact ((isUnit_of_invertible _).mul hunit).mul (isUnit_of_invertible _)

end TauCeti
