/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.LinearAlgebra.Matrix.SchurComplement
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Determinant inequalities for positive-semidefinite matrices

The determinant is monotone on the positive-semidefinite cone. Hadamard--Fischer
bounds a block determinant by the product of its diagonal-block determinants.
The overlapping-block version is the local Gram determinant inequality used
when comparing the Euclidean volumes of an intersection and a sum of subspaces.
The monotonicity and block statements include singular matrices and empty blocks,
over either real or complex scalars.

For real positive-semidefinite `n × n` matrices, the inequality of arithmetic and
geometric means for the eigenvalues gives `det A ≤ (tr A / n) ^ n`, and its mixed
form `det A * det B ≤ (tr (A * B) / n) ^ n` is the pointwise step of the
Aleksandrov–Bakelman–Pucci maximum principle.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §7.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, §6.1, (6.12), for the subspace-height application.
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 m n p : Type*} [RCLike 𝕜]

section Monotonicity

variable [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜}

/-- Adding a positive-semidefinite matrix to the identity cannot decrease its determinant. -/
theorem PosSemidef.one_le_det_one_add (hB : B.PosSemidef) : 1 ≤ (1 + B).det := by
  have hpencil : 1 + B = 1 - (-1 : 𝕜) • B := by simp
  rw [hpencil, hB.isHermitian.det_one_sub_smul]
  simpa using Finset.one_le_prod₀ (s := Finset.univ)
    (f := fun i ↦ (1 : 𝕜) + (hB.isHermitian.eigenvalues i : 𝕜))
    (fun i _ ↦ le_add_of_nonneg_right (RCLike.ofReal_nonneg.mpr
      (hB.eigenvalues_nonneg i)))

/-- Adding a positive-semidefinite matrix cannot decrease the determinant of a
positive-semidefinite matrix, including when the first matrix is singular. -/
theorem PosSemidef.det_le_det_add (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det ≤ (A + B).det := by
  by_cases hdet : A.det = 0
  · rw [hdet]
    exact (hA.add hB).det_nonneg
  let N := CFC.sqrt B * A⁻¹ * CFC.sqrt B
  have hroot : (CFC.sqrt B).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have hN : N.PosSemidef := by
    simpa only [hroot.eq] using hA.inv.mul_mul_conjTranspose_same (CFC.sqrt B)
  have hpencil : (1 + N).det = (1 + A⁻¹ * B).det := by
    simpa using hB.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul A⁻¹ (-1)
  have hfactor : A + B = A * (1 + A⁻¹ * B) := by
    simp [mul_add, ← Matrix.mul_assoc, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)]
  calc
    A.det = A.det * 1 := (mul_one _).symm
    _ ≤ A.det * (1 + N).det :=
      mul_le_mul_of_nonneg_left hN.one_le_det_one_add hA.det_nonneg
    _ = (A + B).det := by rw [hpencil, hfactor, det_mul]

/-- The determinant is monotone for the Loewner order on positive-semidefinite matrices. -/
theorem PosSemidef.det_le_det (hA : A.PosSemidef) (hAB : A ≤ B) : A.det ≤ B.det := by
  simpa only [add_sub_cancel] using hA.det_le_det_add (Matrix.le_iff.mp hAB)

end Monotonicity

section Blocks

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Hadamard--Fischer inequality.** The determinant of a positive-semidefinite
block matrix is at most the product of the diagonal-block determinants. -/
theorem PosSemidef.det_fromBlocks_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {D : Matrix n n 𝕜} (h : (fromBlocks A B Bᴴ D).PosSemidef) :
    (fromBlocks A B Bᴴ D).det ≤ A.det * D.det := by
  have hA : A.PosSemidef := by simpa using h.toBlocks₁₁
  have hD : D.PosSemidef := by simpa using h.toBlocks₂₂
  by_cases hdet : (fromBlocks A B Bᴴ D).det = 0
  · rw [hdet]
    exact mul_nonneg hA.det_nonneg hD.det_nonneg
  have hA' : A.PosDef := by
    simpa only [← toBlocks₁₁_eq_submatrix, toBlocks_fromBlocks₁₁] using
      (h.posDef_iff_det_ne_zero.mpr hdet).submatrix Sum.inl_injective
  cases hA'.isUnit.nonempty_invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    h.schur_complement₁₁ hA.inv.isHermitian (by simp)
  have hbound : (D - Bᴴ * A⁻¹ * B).det ≤ D.det := by
    simpa only [sub_add_cancel] using
      hS.det_le_det_add (hA.inv.conjTranspose_mul_mul_same B)
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  exact mul_le_mul_of_nonneg_left hbound hA.det_nonneg

variable [Fintype p] [DecidableEq p]

/-- **Koteljanskii's inequality for overlapping blocks.** The product of the
principal minors on the common block and on all three blocks is bounded by the
product of the two intermediate principal minors. No block need be nonsingular. -/
theorem PosSemidef.det_mul_det_fromBlocks_le
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix m p 𝕜}
    {D : Matrix n n 𝕜} {E : Matrix n p 𝕜} {F : Matrix p p 𝕜}
    (h : (fromBlocks A (fromCols B C) (fromCols B C)ᴴ
      (fromBlocks D E Eᴴ F)).PosSemidef) :
    A.det * (fromBlocks A (fromCols B C) (fromCols B C)ᴴ
      (fromBlocks D E Eᴴ F)).det ≤
      (fromBlocks A B Bᴴ D).det * (fromBlocks A C Cᴴ F).det := by
  have hA : A.PosSemidef := by simpa using h.toBlocks₁₁
  obtain ⟨hAB, hAC⟩ := h.overlapping_blocks
  by_cases hdet : A.det = 0
  · rw [hdet, zero_mul]
    exact mul_nonneg hAB.det_nonneg hAC.det_nonneg
  -- Eliminate the common block; Fischer's inequality applies to the two residual blocks.
  cases (hA.posDef_iff_det_ne_zero.mpr hdet).isUnit.nonempty_invertible
  have hS := h.schur_complement₁₁ hA.inv.isHermitian (by simp)
  have hblock : fromBlocks D E Eᴴ F - (fromCols B C)ᴴ * A⁻¹ * fromCols B C =
      fromBlocks (D - Bᴴ * A⁻¹ * B) (E - Bᴴ * A⁻¹ * C)
        (E - Bᴴ * A⁻¹ * C)ᴴ (F - Cᴴ * A⁻¹ * C) := by
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      conjTranspose_sub, conjTranspose_mul,
      conjTranspose_conjTranspose, hA.inv.isHermitian.eq]
    ext i j
    cases i <;> cases j <;> simp [Matrix.mul_assoc]
  rw [hblock] at hS
  have hbound := hS.det_fromBlocks_le
  rw [det_fromBlocks₁₁, det_fromBlocks₁₁, det_fromBlocks₁₁,
    invOf_eq_nonsing_inv, hblock]
  calc
    A.det * (A.det * (fromBlocks (D - Bᴴ * A⁻¹ * B) (E - Bᴴ * A⁻¹ * C)
        (E - Bᴴ * A⁻¹ * C)ᴴ (F - Cᴴ * A⁻¹ * C)).det) =
        (A.det * A.det) * (fromBlocks (D - Bᴴ * A⁻¹ * B) (E - Bᴴ * A⁻¹ * C)
          (E - Bᴴ * A⁻¹ * C)ᴴ (F - Cᴴ * A⁻¹ * C)).det := by ring
    _ ≤ (A.det * A.det) * ((D - Bᴴ * A⁻¹ * B).det * (F - Cᴴ * A⁻¹ * C).det) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hA.det_nonneg hA.det_nonneg)
    _ = (A.det * (D - Bᴴ * A⁻¹ * B).det) *
        (A.det * (F - Cᴴ * A⁻¹ * C).det) := by ring

end Blocks

section ArithmeticMean

variable [Fintype n] [DecidableEq n]

/-- **The determinant–trace inequality.** The determinant of a real positive-semidefinite
`n × n` matrix is at most the `n`-th power of the mean of its eigenvalues,
`det A ≤ (tr A / n) ^ n`: the inequality of arithmetic and geometric means for the eigenvalues.
For `n = 0` both sides are `1`. -/
theorem PosSemidef.det_le_trace_div_card_pow {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ (A.trace / Fintype.card n) ^ Fintype.card n := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  set μ := hA.isHermitian.eigenvalues
  have hμ := hA.eigenvalues_nonneg
  have hdet : A.det = ∏ i, μ i := by simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have htr : A.trace = ∑ i, μ i := by simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hcard : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (Fintype.card n : ℝ)⁻¹) μ (fun _ _ => by positivity)
    (by simp [Finset.card_univ, hcard]) fun i _ => hμ i
  rw [Real.finsetProd_rpow _ _ fun i _ => hμ i, ← Finset.mul_sum, ← div_eq_inv_mul] at hamgm
  have hprod : 0 ≤ ∏ i, μ i := Finset.prod_nonneg fun i _ => hμ i
  rw [hdet, htr, ← Real.rpow_inv_natCast_pow hprod (Fintype.card_ne_zero (α := n))]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hprod _) hamgm _

/-- **The mixed determinant–trace inequality.** For real positive-semidefinite `n × n` matrices
`A` and `B`, `det A * det B ≤ (tr (A * B) / n) ^ n`. -/
theorem PosSemidef.det_mul_det_le_trace_mul_div_card_pow {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * B.det ≤ ((A * B).trace / Fintype.card n) ^ Fintype.card n := by
  set S := CFC.sqrt A
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hN : (S * B * S).PosSemidef := by
    simpa only [hS.eq] using hB.mul_mul_conjTranspose_same S
  have hdet : (S * B * S).det = A.det * B.det := by
    rw [← CFC.sqrt_mul_sqrt_self A hA.nonneg]
    simp only [det_mul, S]
    ring
  rw [← hdet, ← trace_mul_comm, ← hA.trace_sqrt_mul_mul_sqrt]
  exact hN.det_le_trace_div_card_pow

end ArithmeticMean

end Matrix
