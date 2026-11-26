/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic

import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The resolvent of a Hermitian dilation

For a rectangular matrix `A`, the resolvent of the Hermitian block matrix
`D = [[0, Aᴴ], [A, 0]]` has diagonal blocks `z (AᴴA - z² I)⁻¹` and
`z (AAᴴ - z² I)⁻¹`. Its off-diagonal blocks use the same two Gram resolvents.
This identity lets the resolvent method for singular values work with a matrix linear
in the entries of `A`.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probability Surveys 9 (2012),
  Lemma 4.19.
-/

public section

noncomputable section

namespace Matrix

variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- The resolvent of the Hermitian dilation of a rectangular matrix, expressed in terms of the
resolvents of its two Gram matrices. -/
theorem inv_fromBlocks_zero_conjTranspose_sub_smul_one (A : Matrix m n 𝕜) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    let P := (Aᴴ * A - z ^ 2 • 1)⁻¹
    let Q := (A * Aᴴ - z ^ 2 • 1)⁻¹
    (fromBlocks 0 Aᴴ A 0 - z • 1)⁻¹ = fromBlocks (z • P) (Aᴴ * Q) (A * P) (z • Q) := by
  dsimp only
  let D := fromBlocks 0 Aᴴ A 0
  let P := Aᴴ * A - z ^ 2 • 1
  let Q := A * Aᴴ - z ^ 2 • 1
  have hd : D.IsHermitian := IsHermitian.fromBlocks isHermitian_zero
    (conjTranspose_conjTranspose A) isHermitian_zero
  have hblock (w : 𝕜) : D + w • 1 = fromBlocks (w • 1) Aᴴ A (w • 1) := by
    simp [D, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  have hminus : D - z • 1 = fromBlocks (-z • 1) Aᴴ A (-z • 1) := by
    rw [sub_eq_add_neg, ← neg_smul, hblock]
  have hfactor : (D - z • 1) * (D + z • 1) = fromBlocks P 0 0 Q := by
    rw [hminus, hblock, fromBlocks_multiply]
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, P, Q, pow_two, sub_eq_add_neg, add_comm]
  have hunit : IsUnit (fromBlocks P 0 0 Q) := hfactor ▸
    (hd.isUnit_sub_smul_one_of_im_ne_zero hz).mul
      (by simpa only [map_neg, neg_ne_zero, neg_smul, sub_neg_eq_add] using
        hd.isUnit_sub_smul_one_of_im_ne_zero (z := -z) (by simpa using hz))
  obtain ⟨hp, hq⟩ := isUnit_fromBlocks_zero₂₁.mp hunit
  have hinv : (D - z • 1)⁻¹ = (D + z • 1) * fromBlocks P⁻¹ 0 0 Q⁻¹ := by
    apply inv_eq_right_inv
    rw [← Matrix.mul_assoc, hfactor, fromBlocks_multiply]
    simp [mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hp),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hq), fromBlocks_one]
  rw [hinv, hblock, fromBlocks_multiply]
  simp [P, Q]

end Matrix
