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
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive

import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.LinearAlgebra.Matrix.Vec

/-!
# Determinant inequalities for positive-semidefinite matrices

The determinant is monotone on the positive-semidefinite cone. Hadamard--Fischer
bounds a block determinant by the product of its diagonal-block determinants.
The overlapping-block version is the local Gram determinant inequality used
when comparing the Euclidean volumes of an intersection and a sum of subspaces.
The monotonicity and block statements include singular matrices and empty blocks,
over either real or complex scalars.

For positive-semidefinite `n × n` matrices `A` and `B` over `ℝ` or `ℂ`, the inequality of
arithmetic and geometric means for the eigenvalues (`Real.geom_mean_le_arith_mean_weighted`)
gives `n * (Re det A) ^ (1 / n) ≤ Re tr A`, with equality exactly for real multiples of `1`
(`Real.geom_mean_eq_arith_mean_weighted_iff_of_pos`, with
`Matrix.IsHermitian.eq_smul_one_of_eigenvalues_eq` from the spectral theorem), and the mixed
form `n * (Re (det A * det B)) ^ (1 / n) ≤ Re tr (A * B)`, applied to `√A * B * √A`. For
positive-definite `A` equality holds exactly when `B` is a real multiple of `A⁻¹`. The mixed
bound turns a lower bound on `det A * det B` into a lower bound on the trace pairing
`Re tr (A * B)`, as in the complex Hessian equation estimates. Determinants and traces of
Hermitian matrices are real; the statements take their real parts. Over `ℝ` the power forms
`det A ≤ (tr A / n) ^ n` and `det A * det B ≤ (tr (A * B) / n) ^ n` follow; the latter is the
pointwise step of the Aleksandrov–Bakelman–Pucci maximum principle. Read through the standard
basis of `ℝⁿ`, it bounds `det T det A` by `(∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ / n)ⁿ` for a positive operator `T`
(`LinearMap.IsPositive.det_mul_det_le_sum_mul_apply_div_card_pow`), where the principal part
`∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ = tr (A M_T)` (`LinearMap.IsSymmetric.trace_mul_toMatrix`) is nonnegative
(`LinearMap.IsPositive.sum_mul_apply_nonneg`).

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §7.8.
* B. Guo, D. H. Phong and F. Tong, *On L^∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), for the trace–determinant inequality and its equality case.
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

/-- **The determinant–trace inequality.** For a positive-semidefinite `n × n` matrix `N`,
`n * (Re det N) ^ (1 / n) ≤ Re tr N`. For `n = 0` both sides are `0`. -/
theorem PosSemidef.card_mul_re_det_rpow_le_re_trace {N : Matrix n n 𝕜} (hN : N.PosSemidef) :
    Fintype.card n * RCLike.re N.det ^ (Fintype.card n : ℝ)⁻¹ ≤ RCLike.re N.trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  set μ := hN.isHermitian.eigenvalues
  have hμ := hN.eigenvalues_nonneg
  have hcard : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (Fintype.card n : ℝ)⁻¹) μ (fun _ _ => by positivity)
    (by simp [Finset.card_univ, hcard]) fun i _ => hμ i
  rw [Real.finsetProd_rpow _ _ fun i _ => hμ i, ← Finset.mul_sum] at hamgm
  rw [hN.isHermitian.re_det_eq_prod_eigenvalues, hN.isHermitian.re_trace_eq_sum_eigenvalues]
  calc (Fintype.card n : ℝ) * (∏ i, μ i) ^ (Fintype.card n : ℝ)⁻¹
      ≤ Fintype.card n * ((Fintype.card n : ℝ)⁻¹ * ∑ i, μ i) := by gcongr
    _ = ∑ i, μ i := by field_simp

/-- **The equality case of the determinant–trace inequality.** For a positive-semidefinite
`n × n` matrix `N`, `n * (Re det N) ^ (1 / n) = Re tr N` exactly when `N` is a real multiple
of `1`. -/
theorem PosSemidef.card_mul_re_det_rpow_eq_re_trace_iff {N : Matrix n n 𝕜}
    (hN : N.PosSemidef) :
    Fintype.card n * RCLike.re N.det ^ (Fintype.card n : ℝ)⁻¹ = RCLike.re N.trace ↔
      ∃ c : ℝ, N = c • (1 : Matrix n n 𝕜) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => by simp⟩
  have i₀ : n := Classical.arbitrary n
  have hcard : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun h => ?_, ?_⟩
  · set μ := hN.isHermitian.eigenvalues
    have hμ := hN.eigenvalues_nonneg
    have hamgm := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ
      (fun _ => (Fintype.card n : ℝ)⁻¹) μ (fun _ _ => by positivity)
      (by simp [Finset.card_univ, hcard]) fun i _ => hμ i
    rw [Real.finsetProd_rpow _ _ fun i _ => hμ i, ← Finset.mul_sum] at hamgm
    rw [hN.isHermitian.re_det_eq_prod_eigenvalues, hN.isHermitian.re_trace_eq_sum_eigenvalues]
      at h
    have hμc := hamgm.1 (by rw [← h]; field_simp)
    exact ⟨μ i₀, hN.isHermitian.eq_smul_one_of_eigenvalues_eq fun i =>
      hμc i (Finset.mem_univ _) i₀ (Finset.mem_univ _)⟩
  · rintro ⟨c, rfl⟩
    have hc : 0 ≤ c := by
      simpa [RCLike.real_smul_eq_coe_mul] using hN.diag_nonneg (i := i₀)
    simp only [det_smul_of_tower, det_one, trace_smul, trace_one, RCLike.smul_re, RCLike.one_re,
      mul_one, RCLike.natCast_re]
    rw [Real.pow_rpow_inv_natCast hc Fintype.card_ne_zero, mul_comm]

/-- **The trace–determinant inequality.** For positive-semidefinite `n × n` matrices `A` and `B`,
`n * (Re (det A * det B)) ^ (1 / n) ≤ Re tr (A * B)`. -/
theorem PosSemidef.card_mul_re_det_mul_det_rpow_le_re_trace_mul {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Fintype.card n * RCLike.re (A.det * B.det) ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A * B).trace := by
  rw [← hA.det_sqrt_mul_mul_sqrt, ← trace_mul_comm, ← hA.trace_sqrt_mul_mul_sqrt]
  exact (hB.sqrt_mul_mul_sqrt A).card_mul_re_det_rpow_le_re_trace

/-- **The equality case of the trace–determinant inequality.** For a positive-definite `A` and a
positive-semidefinite `B`, `n * (Re (det A * det B)) ^ (1 / n) = Re tr (A * B)` exactly when `B`
is a real multiple of `A⁻¹`. -/
theorem PosDef.card_mul_re_det_mul_det_rpow_eq_re_trace_mul_iff {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    Fintype.card n * RCLike.re (A.det * B.det) ^ (Fintype.card n : ℝ)⁻¹ =
      RCLike.re (A * B).trace ↔ ∃ c : ℝ, B = c • A⁻¹ := by
  rw [← hA.posSemidef.det_sqrt_mul_mul_sqrt, ← trace_mul_comm,
    ← hA.posSemidef.trace_sqrt_mul_mul_sqrt,
    (hB.sqrt_mul_mul_sqrt A).card_mul_re_det_rpow_eq_re_trace_iff]
  set S := CFC.sqrt A
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSu : IsUnit S.det := hA.isUnit_det_sqrt
  have hAinv : A⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, mul_inv_rev]
  -- `X ↦ S⁻¹ * X * S⁻¹` inverts the conjugation `B ↦ S * B * S`.
  have hconj (X : Matrix n n 𝕜) : S⁻¹ * (S * X * S) * S⁻¹ = X := by
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSu, Matrix.mul_one]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · have h := congrArg (fun X => S⁻¹ * X * S⁻¹) hc
    simp only [hconj] at h
    simp [h, hAinv]
  · simp [hc, hAinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSu,
      Matrix.nonsing_inv_mul _ hSu]

/-- **The determinant–trace inequality in power form.** The determinant of a real
positive-semidefinite `n × n` matrix is at most the `n`-th power of the mean of its eigenvalues,
`det A ≤ (tr A / n) ^ n`. For `n = 0` both sides are `1`. -/
theorem PosSemidef.det_le_trace_div_card_pow {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ (A.trace / Fintype.card n) ^ Fintype.card n := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  exact Real.le_div_pow_of_mul_rpow_inv_le Fintype.card_ne_zero hA.det_nonneg
    (by simpa only [RCLike.re_to_real] using hA.card_mul_re_det_rpow_le_re_trace)

/-- **The mixed determinant–trace inequality in power form.** For real positive-semidefinite
`n × n` matrices `A` and `B`, `det A * det B ≤ (tr (A * B) / n) ^ n`. -/
theorem PosSemidef.det_mul_det_le_trace_mul_div_card_pow {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.det * B.det ≤ ((A * B).trace / Fintype.card n) ^ Fintype.card n := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  exact Real.le_div_pow_of_mul_rpow_inv_le Fintype.card_ne_zero
    (mul_nonneg hA.det_nonneg hB.det_nonneg)
    (by simpa only [RCLike.re_to_real] using hA.card_mul_re_det_mul_det_rpow_le_re_trace_mul hB)

end ArithmeticMean

end Matrix

namespace LinearMap

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a symmetric operator `T` on `ℝⁿ`, the trace of `A` times the matrix of `T` is
`∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ`. -/
theorem IsSymmetric.trace_mul_toMatrix {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι}
    (hT : T.IsSymmetric) (A : Matrix ι ι ℝ) :
    (A * LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis T).trace =
      ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i := by
  have hsym (i j : ι) :
      T (EuclideanSpace.single i 1) j = T (EuclideanSpace.single j 1) i := by
    simpa [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left] using
      hT (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, hsym]

/-- **The principal part of a positive operator.** If `T` is a positive operator on `ℝⁿ` and `A`
is positive semidefinite, then `0 ≤ ∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ`. -/
theorem IsPositive.sum_mul_apply_nonneg
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} (hT : T.IsPositive) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : 0 ≤ ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i := by
  rw [← hT.isSymmetric.trace_mul_toMatrix]
  simpa using
    hA.trace_transpose_mul_mul_mul_nonneg ((LinearMap.posSemidef_toMatrix_iff _).2 hT)
      (1 : Matrix ι ι ℝ)

/-- **The determinant bound for a positive operator.** If `T` is a positive operator on `ℝⁿ` and
`A` is positive semidefinite, then `det T det A ≤ (∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ / n)ⁿ`: the determinant–trace
inequality `Matrix.PosSemidef.det_mul_det_le_trace_mul_div_card_pow` for `A` and the matrix of
`T`. Applied to `T = -D²u` on the upper contact set, it bounds the Hessian determinant by the
elliptic operator. -/
theorem IsPositive.det_mul_det_le_sum_mul_apply_div_card_pow
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} (hT : T.IsPositive) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    LinearMap.det T * A.det ≤
      ((∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i) / Fintype.card ι) ^
        Fintype.card ι := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis, mul_comm,
    ← hT.isSymmetric.trace_mul_toMatrix]
  exact hA.det_mul_det_le_trace_mul_div_card_pow ((LinearMap.posSemidef_toMatrix_iff _).2 hT)

end LinearMap
