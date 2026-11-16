/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.Determinant
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Hadamard's determinant inequality and diagonal quadratic lower bounds

For a positive-semidefinite matrix `A` over `ℝ` or `ℂ`, **Hadamard's determinant inequality**
bounds the determinant by the product of the diagonal entries: `A.det ≤ ∏ i, A i i`, including when
`A` is singular or the index type is empty.

When a positive-definite real matrix `B` satisfies a converse Hadamard bound
`∏ i, B i i ≤ D * B.det` (as reduced Gram matrices do), Hadamard's inequality on the complementary
principal minor bounds each inverse diagonal entry `(B⁻¹) k k` by `D / B k k`, yielding the
quantitative quadratic lower bound `a k ^ 2 * B k k / D ≤ a ⬝ᵥ B *ᵥ a` for every vector `a` and
coordinate `k`.

## Main results

* `Matrix.PosSemidef.det_le_prod_diag`: Hadamard's determinant inequality `A.det ≤ ∏ i, A i i`.
* `Matrix.PosDef.inv_apply_self_le_div`: `(B⁻¹) k k ≤ D / B k k` when `∏ i, B i i ≤ D * B.det`.
* `Matrix.PosDef.sq_mul_apply_self_div_le_dotProduct_mulVec`:
  `a k ^ 2 * B k k / D ≤ a ⬝ᵥ B *ᵥ a` when `∏ i, B i i ≤ D * B.det`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.8.1 (Hadamard's inequality).
* B. Bakker, B. Klingler, and J. Tsimerman, *Tame topology of arithmetic quotients and
  algebraicity of Hodge loci*, J. Amer. Math. Soc. 33 (2020), 917–939, §4.5, Definition 4.11.
-/

public section

open scoped ComplexOrder Matrix

namespace Matrix

/-- **Hadamard's determinant inequality.** The determinant of a positive-semidefinite matrix over
`ℝ` or `ℂ` is at most the product of its diagonal entries, including when the matrix is singular
or the index type is empty. -/
theorem PosSemidef.det_le_prod_diag {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  generalize hk : Fintype.card n = k
  induction k generalizing n with
  | zero =>
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hk
    simp
  | succ k ih =>
    obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    let e := Equiv.sumCompl (· = i)
    set A₁₁ : Matrix {a // a = i} {a // a = i} 𝕜 := A.submatrix (↑) (↑)
    set A₁₂ : Matrix {a // a = i} {a // a ≠ i} 𝕜 := A.submatrix (↑) (↑)
    set A₂₂ : Matrix {a // a ≠ i} {a // a ≠ i} 𝕜 := A.submatrix (↑) (↑)
    have hblk : A.submatrix e e = fromBlocks A₁₁ A₁₂ A₁₂ᴴ A₂₂ := by
      ext (x | x) (y | y)
      · rfl
      · rfl
      · exact (hA.isHermitian.apply x.1 y.1).symm
      · rfl
    have hcard : Fintype.card {a // a ≠ i} = k := by
      rw [Fintype.card_of_subtype (Finset.univ.erase i) (by simp),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hk, Nat.add_sub_cancel]
    have hdet₁₁ : A₁₁.det = A i i := by rw [det_unique]; simp [A₁₁, (default : {a // a = i}).2]
    have hsub : (fromBlocks A₁₁ A₁₂ A₁₂ᴴ A₂₂).PosSemidef := hblk ▸ hA.submatrix e
    calc A.det = (fromBlocks A₁₁ A₁₂ A₁₂ᴴ A₂₂).det := by rw [← hblk, det_submatrix_equiv_self]
      _ ≤ A i i * A₂₂.det := hdet₁₁ ▸ hsub.det_fromBlocks_le
      _ ≤ A i i * ∏ j : {a // a ≠ i}, A j j :=
          mul_le_mul_of_nonneg_left (ih (hA.submatrix (Subtype.val : {a // a ≠ i} → n)) hcard)
            (by simpa using hA.dotProduct_mulVec_nonneg (Pi.single i 1))
      _ = ∏ j, A j j := by
          rw [← Finset.prod_subtype (Finset.univ.erase i) (by simp) (fun j ↦ A j j),
            Finset.mul_prod_erase Finset.univ (fun a ↦ A a a) (Finset.mem_univ i)]

/-- If a positive-definite real matrix `B` satisfies `∏ i, B i i ≤ D * B.det`, then every diagonal
entry of `B⁻¹` satisfies `(B⁻¹) k k ≤ D / B k k`. -/
theorem PosDef.inv_apply_self_le_div {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.PosDef) {D : ℝ} (hD : ∏ i, B i i ≤ D * B.det) (k : n) :
    B⁻¹ k k ≤ D / B k k := by
  set B' : Matrix {a // a ≠ k} {a // a ≠ k} ℝ := B.submatrix (↑) (↑)
  have hB'_le : B k k * B'.det ≤ D * B.det := calc
    B k k * B'.det ≤ B k k * ∏ j : {a // a ≠ k}, B j j :=
      mul_le_mul_of_nonneg_left
        (hB.submatrix Subtype.val_injective).posSemidef.det_le_prod_diag hB.diag_pos.le
    _ = ∏ i, B i i := by
      rw [← Finset.prod_subtype (Finset.univ.erase k) (by simp) (fun i ↦ B i i),
        Finset.mul_prod_erase Finset.univ (fun a ↦ B a a) (Finset.mem_univ k)]
    _ ≤ D * B.det := hD
  rw [inv_def, Matrix.smul_apply, B.adjugate_apply_self k, Ring.inverse_eq_inv', smul_eq_mul,
    ← div_eq_inv_mul, div_le_div_iff₀ hB.det_pos hB.diag_pos]
  linarith

/-- **Lower bound on a positive-definite quadratic form by its diagonal entries.** If `B` is a
positive-definite real matrix with `∏ i, B i i ≤ D * B.det`, then every vector `a : n → ℝ` and
index `k : n` satisfy `a k ^ 2 * B k k / D ≤ a ⬝ᵥ B *ᵥ a`. -/
theorem PosDef.sq_mul_apply_self_div_le_dotProduct_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.PosDef) {D : ℝ} (hD : ∏ i, B i i ≤ D * B.det)
    (a : n → ℝ) (k : n) :
    a k ^ 2 * B k k / D ≤ a ⬝ᵥ B *ᵥ a := by
  have hinv_pos : 0 < B⁻¹ k k := hB.inv.diag_pos
  set u : n → ℝ := B⁻¹ *ᵥ Pi.single k 1
  have hBu : B *ᵥ u = Pi.single k 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv B hB.det_pos.ne'.isUnit, one_mulVec]
  have huBu : u ⬝ᵥ B *ᵥ u = B⁻¹ k k := by rw [hBu, dotProduct_single_one]; simp [u]
  have haBu : a ⬝ᵥ B *ᵥ u = a k := by rw [hBu, dotProduct_single_one]
  have huBa : u ⬝ᵥ B *ᵥ a = a k := by rw [hB.isHermitian.isSymm.dotProduct_mulVec_comm, haBu]
  have hnonneg : 0 ≤ (a - (a k / B⁻¹ k k) • u) ⬝ᵥ B *ᵥ (a - (a k / B⁻¹ k k) • u) := by
    simpa only [star_trivial] using
      hB.posSemidef.dotProduct_mulVec_nonneg (a - (a k / B⁻¹ k k) • u)
  have hexpand : (a - (a k / B⁻¹ k k) • u) ⬝ᵥ B *ᵥ (a - (a k / B⁻¹ k k) • u) =
      a ⬝ᵥ B *ᵥ a - a k ^ 2 / B⁻¹ k k := by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, haBu, huBa, huBu]
    field_simp [hinv_pos.ne']
    ring
  calc a k ^ 2 * B k k / D = a k ^ 2 / (D / B k k) := by rw [div_div_eq_mul_div]
    _ ≤ a k ^ 2 / B⁻¹ k k :=
        div_le_div_of_nonneg_left (sq_nonneg _) hinv_pos (hB.inv_apply_self_le_div hD k)
    _ ≤ a ⬝ᵥ B *ᵥ a := sub_nonneg.mp (hexpand ▸ hnonneg)

end Matrix
