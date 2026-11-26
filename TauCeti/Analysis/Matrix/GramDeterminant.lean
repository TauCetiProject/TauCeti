/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.Matrix.PosSemidef.Determinant

/-!
# Cauchy–Schwarz inequality for Gram determinants

For a positive-semidefinite block matrix `fromBlocks A B Bᴴ D` with square blocks of the same size
over `𝕜 = ℝ` or `ℂ`, the off-diagonal determinant satisfies `‖B.det‖ ^ 2 ≤ ‖A.det‖ * ‖D.det‖`
(`Matrix.PosSemidef.norm_det_sq_le_of_fromBlocks`).

Specializing to `(fromCols A B)ᴴ * G * fromCols A B` for a positive-semidefinite matrix `G` yields
the Cauchy–Schwarz inequality for Gram pairings in both matrix form
(`Matrix.PosSemidef.norm_det_conjTranspose_mul_mul_sq_le`) and vector-family form
(`Matrix.PosSemidef.norm_det_pairing_sq_le`):
`‖det (vᵢ* G wₖ)‖² ≤ ‖det (vᵢ* G vₖ)‖ · ‖det (wᵢ* G wₖ)‖`.

## Main results

* `Matrix.PosSemidef.norm_det_sq_le_of_fromBlocks`: `‖B.det‖ ^ 2 ≤ ‖A.det‖ * ‖D.det‖` for a
  positive-semidefinite `2 × 2` block matrix `fromBlocks A B Bᴴ D`.
* `Matrix.PosSemidef.norm_det_conjTranspose_mul_mul_sq_le`:
  `‖(Aᴴ * G * B).det‖ ^ 2 ≤ ‖(Aᴴ * G * A).det‖ * ‖(Bᴴ * G * B).det‖` for `G.PosSemidef`.
* `Matrix.PosSemidef.norm_det_pairing_sq_le`:
  `‖det (star (v i) ⬝ᵥ G *ᵥ w k)‖ ^ 2 ≤ ‖det (star (v i) ⬝ᵥ G *ᵥ v k)‖ *`
  `‖det (star (w i) ⬝ᵥ G *ᵥ w k)‖` for `G.PosSemidef`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013, §7.8.
* Adapted from `New.norm_det_pairing_sq_le` in `src/Lib/General/LinearAlgebra/GramDeterminant.lean`
  of grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix.PosSemidef

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **Off-diagonal determinant Cauchy–Schwarz inequality.** For a positive-semidefinite `2 × 2`
block matrix `fromBlocks A B Bᴴ D` with square blocks of the same size over `ℝ` or `ℂ`,
`‖B.det‖ ^ 2 ≤ ‖A.det‖ * ‖D.det‖`. -/
theorem norm_det_sq_le_of_fromBlocks {A B D : Matrix n n 𝕜}
    (h : (fromBlocks A B Bᴴ D).PosSemidef) :
    ‖B.det‖ ^ 2 ≤ ‖A.det‖ * ‖D.det‖ := by
  have hA : A.PosSemidef := by simpa using h.toBlocks₁₁
  have hD : D.PosSemidef := by simpa using h.toBlocks₂₂
  by_cases hdet : A.det = 0
  · obtain ⟨x, hx0, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hBx : Bᴴ *ᵥ x = 0 := by simpa using h.toBlocks₂₁_mulVec_eq_zero (by simpa using hAx)
    have hBdet : B.det = 0 := by
      have h' : Bᴴ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx0, hBx⟩
      simpa using h'
    simp [hBdet, hdet]
  have hA' : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hdet
  cases hA'.isUnit.nonempty_invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef := h.schur_complement₁₁ hA.inv.isHermitian (by simp)
  have hle : (Bᴴ * A⁻¹ * B).det ≤ D.det :=
    (hA.inv.conjTranspose_mul_mul_same B).det_le_det (Matrix.le_iff.2 hS)
  have h_eq_of_nonneg {z : 𝕜} (hz : 0 ≤ z) : (‖z‖ : 𝕜) = z := by
    obtain ⟨hre, him⟩ := RCLike.nonneg_iff.1 hz
    have hz_eq : (RCLike.re z : 𝕜) = z := by apply RCLike.ext <;> simp [him]
    rw [← hz_eq, RCLike.norm_ofReal, abs_of_nonneg hre]
  have hA_eq : (‖A.det‖ : 𝕜) = A.det := h_eq_of_nonneg hA.det_nonneg
  have hD_eq : (‖D.det‖ : 𝕜) = D.det := h_eq_of_nonneg hD.det_nonneg
  have h_lhs : RCLike.re (Bᴴ * A⁻¹ * B).det = ‖A.det‖⁻¹ * ‖B.det‖ ^ 2 := by
    rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv']
    conv_lhs => rw [← hA_eq]
    rw [← RCLike.ofReal_inv, mul_right_comm, RCLike.star_def, RCLike.conj_mul,
      ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re, mul_comm]
  have hle_re : ‖A.det‖⁻¹ * ‖B.det‖ ^ 2 ≤ ‖D.det‖ := by
    have h1 : 0 ≤ RCLike.re (D.det - (Bᴴ * A⁻¹ * B).det) :=
      (RCLike.nonneg_iff.1 (sub_nonneg.2 hle)).1
    rw [map_sub, h_lhs, sub_nonneg] at h1
    rwa [← hD_eq, RCLike.ofReal_re] at h1
  exact (inv_mul_le_iff₀ (norm_pos_iff.2 hdet)).1 hle_re

/-- **Cauchy–Schwarz inequality for Gram determinants (matrix form).** For a positive-semidefinite
matrix `G : Matrix m m 𝕜` and matrices `A B : Matrix m n 𝕜` over `ℝ` or `ℂ`,
`‖(Aᴴ * G * B).det‖ ^ 2 ≤ ‖(Aᴴ * G * A).det‖ * ‖(Bᴴ * G * B).det‖`. -/
theorem norm_det_conjTranspose_mul_mul_sq_le [Fintype m] {G : Matrix m m 𝕜} (hG : G.PosSemidef)
    (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * G * B).det‖ ^ 2 ≤ ‖(Aᴴ * G * A).det‖ * ‖(Bᴴ * G * B).det‖ := by
  have hblock :
      fromBlocks (Aᴴ * G * A) (Aᴴ * G * B) (Aᴴ * G * B)ᴴ (Bᴴ * G * B) =
        (fromCols A B)ᴴ * G * fromCols A B := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, mul_fromCols,
      conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG.isHermitian.eq]
    ext i j
    cases i <;> cases j <;> simp [Matrix.mul_assoc]
  exact (hblock ▸ hG.conjTranspose_mul_mul_same (fromCols A B)).norm_det_sq_le_of_fromBlocks

/-- **Cauchy–Schwarz inequality for Gram determinants (vector-family form).** For a
positive-semidefinite matrix `G : Matrix m m 𝕜` and two families `v w : n → m → 𝕜` of vectors over
`ℝ` or `ℂ`, `‖det (star (v i) ⬝ᵥ G *ᵥ w k)‖ ^ 2 ≤`
`‖det (star (v i) ⬝ᵥ G *ᵥ v k)‖ * ‖det (star (w i) ⬝ᵥ G *ᵥ w k)‖`. -/
theorem norm_det_pairing_sq_le [Fintype m] {G : Matrix m m 𝕜} (hG : G.PosSemidef)
    (v w : n → m → 𝕜) :
    ‖(of fun i k : n ↦ star (v i) ⬝ᵥ G *ᵥ w k).det‖ ^ 2 ≤
      ‖(of fun i k : n ↦ star (v i) ⬝ᵥ G *ᵥ v k).det‖ *
        ‖(of fun i k : n ↦ star (w i) ⬝ᵥ G *ᵥ w k).det‖ := by
  have h_eq (x y : n → m → 𝕜) :
      (of x)ᵀᴴ * G * (of y)ᵀ = of fun i k : n ↦ star (x i) ⬝ᵥ G *ᵥ y k := by
    rw [Matrix.mul_assoc]
    ext i k
    simp [Matrix.mul_apply, dotProduct, mulVec]
  simpa only [h_eq] using hG.norm_det_conjTranspose_mul_mul_sq_le (of v)ᵀ (of w)ᵀ

end Matrix.PosSemidef
