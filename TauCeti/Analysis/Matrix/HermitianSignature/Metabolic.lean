/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Basic

/-!
# Signatures of metabolic Hermitian block forms

A Hermitian matrix with both diagonal blocks zero has signature zero, even when it is
singular or its off-diagonal block is rectangular. A nonsingular Hermitian matrix with a
half-size zero diagonal block also has signature zero: its off-diagonal block is invertible,
and a block shear removes the other diagonal block.

The latter is the linear algebra behind the signature obstruction for metabolic Seifert
forms. Nonsingularity is essential when only one diagonal block vanishes.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 8,
  Theorem 8.19 (the metabolic-form argument for the signature obstruction).

The proofs use `Matrix.IsHermitian.signature_congr` and
`Matrix.IsHermitian.signature_eq_zero_of_congr_neg`.
-/

public section

namespace Matrix

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ]

/-- A Hermitian block matrix with zero diagonal blocks has signature zero. The
off-diagonal block may be rectangular or singular. -/
@[simp]
theorem signature_fromBlocks_zero_diagonal (B : Matrix ι κ 𝕜) :
    (isHermitian_zero.fromBlocks (B := B) rfl isHermitian_zero).signature = 0 := by
  classical
  let P : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜 := Matrix.fromBlocks 1 0 0 (-1)
  have hP : IsUnit P.det := by simp [P, det_neg]
  apply IsHermitian.signature_eq_zero_of_congr_neg hP
  simp [P, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg]

namespace IsHermitian

variable [DecidableEq ι]

/-- A nonsingular Hermitian matrix with a half-size zero diagonal block has signature
zero. No definiteness or nonsingularity is required of its other diagonal block. -/
theorem signature_eq_zero_of_fromBlocks_zero₁₁ {B D : Matrix ι ι 𝕜}
    (hD : D.IsHermitian) (hdet : IsUnit (Matrix.fromBlocks 0 B Bᴴ D).det) :
    (isHermitian_zero.fromBlocks (B := B) rfl hD).signature = 0 := by
  let H := Matrix.fromBlocks 0 B Bᴴ D
  -- The top-left block of H * H⁻¹ = 1 makes B right-invertible.
  have hright : B * H⁻¹.toBlocks₂₁ = 1 := by
    have h : H * Matrix.fromBlocks H⁻¹.toBlocks₁₁ H⁻¹.toBlocks₁₂
        H⁻¹.toBlocks₂₁ H⁻¹.toBlocks₂₂ = 1 := by
      rw [fromBlocks_toBlocks]
      exact H.mul_nonsing_inv hdet
    ext i j
    simpa [H, fromBlocks_multiply, toBlocks₁₁, Matrix.one_apply] using
      congrFun (congrFun (congrArg toBlocks₁₁ h) i) j
  have hB : IsUnit B.det :=
    IsUnit.of_mul_eq_one (H⁻¹.toBlocks₂₁.det) (by rw [← det_mul, hright, det_one])
  let X : Matrix ι ι 𝕜 := (-(2 : 𝕜)⁻¹) • (D * B⁻¹)
  have hXB : X * B = (-(2 : 𝕜)⁻¹) • D := by
    simp only [X, smul_mul, nonsing_inv_mul_cancel_right _ _ hB]
  have hBX : Bᴴ * Xᴴ = (-(2 : 𝕜)⁻¹) • D := by
    have h := congrArg Matrix.conjTranspose hXB
    simpa only [conjTranspose_mul, conjTranspose_smul, star_neg, star_inv₀,
      star_ofNat, hD.eq] using h
  have hcancel : Bᴴ * Xᴴ + (X * B + D) = 0 := by
    rw [hXB, hBX]
    ext i j
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply]
    ring
  let P : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜 := Matrix.fromBlocks 1 0 X 1
  have hP : IsUnit P.det := by simp [P]
  have hcong : P * H * Pᴴ = Matrix.fromBlocks 0 B Bᴴ 0 := by
    simp [P, H, fromBlocks_conjTranspose, fromBlocks_multiply, hcancel]
  have hs := (isHermitian_zero.fromBlocks (B := B) rfl hD).signature_congr hP
  have heq : (isHermitian_zero.fromBlocks (B := B) rfl hD).signature =
      (isHermitian_zero.fromBlocks (B := B) rfl isHermitian_zero).signature := by
    convert hs.symm using 2
    exact hcong.symm
  rw [heq, Matrix.signature_fromBlocks_zero_diagonal]

end IsHermitian

end Matrix
