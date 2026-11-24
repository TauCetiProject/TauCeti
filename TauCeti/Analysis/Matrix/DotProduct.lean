/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Diagonal and off-diagonal decomposition of matrix forms

For a square matrix `A : Matrix n n 𝕜` over an `RCLike` field `𝕜`, the sesquilinear quadratic form
`star v ⬝ᵥ A *ᵥ v` splits into the weighted squared-norm sum `∑ i, A i i * ‖v i‖ ^ 2` and the
off-diagonal form `star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v`
(`Matrix.star_dotProduct_mulVec_eq_sum_diag_add`), with real-part counterpart
`Matrix.re_star_dotProduct_mulVec_eq_sum_diag_add`.

The form of a diagonal matrix is the weighted sum `∑ i, d i * ‖v i‖ ^ 2`
(`Matrix.star_dotProduct_diagonal_mulVec`), and the form of `B * diagonal d * Bᴴ` is the same
sum for the coordinates of `Bᴴ *ᵥ v`
(`Matrix.star_dotProduct_mul_diagonal_mul_conjTranspose_mulVec`). With `B` the eigenvector
unitary of a Hermitian matrix, the latter expands a quadratic form over the eigenbasis.

A Hermitian matrix is determined by its quadratic form: if `star v ⬝ᵥ A *ᵥ v = 0` for every `v`,
then `A = 0` (`Matrix.IsHermitian.forall_star_dotProduct_mulVec_self_eq_zero_iff`). This is
polarization for Hermitian forms, read from Mathlib's
`LinearMap.IsSymmetric.inner_map_self_eq_zero` through `Matrix.toEuclideanLin`.

A nonzero real vector `v` rescaled by the inverse `(√(v ⬝ᵥ v))⁻¹` of its length is a unit vector
(`Matrix.dotProduct_self_inv_sqrt_smul`).
-/

public section

namespace Matrix

/-- A nonzero real vector `v` rescaled by the inverse `(√(v ⬝ᵥ v))⁻¹` of its length is a unit
vector. -/
theorem dotProduct_self_inv_sqrt_smul {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ((√(v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((√(v ⬝ᵥ v))⁻¹ • v) = 1 := by
  have hpos : 0 < v ⬝ᵥ v :=
    (dotProduct_self_nonneg v).lt_of_ne' (dotProduct_self_eq_zero.not.mpr hv)
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  exact (Real.sq_sqrt hpos.le).symm

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

variable [RCLike 𝕜]

/-- The form `star v ⬝ᵥ diagonal d *ᵥ v` is the weighted sum of the squared moduli of the
coordinates of `v`. -/
theorem star_dotProduct_diagonal_mulVec (d v : n → 𝕜) :
    star v ⬝ᵥ diagonal d *ᵥ v = ∑ i, d i * ((‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_left_comm, RCLike.star_def, RCLike.conj_mul]; norm_cast

/-- The form of `B * diagonal d * Bᴴ` at `v` is the weighted sum of the squared moduli of the
coordinates of `Bᴴ *ᵥ v`. -/
theorem star_dotProduct_mul_diagonal_mul_conjTranspose_mulVec {m : Type*} [Fintype m]
    (B : Matrix m n 𝕜) (d : n → 𝕜) (v : m → 𝕜) :
    star v ⬝ᵥ (B * diagonal d * Bᴴ) *ᵥ v = ∑ j, d j * ((‖(Bᴴ *ᵥ v) j‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← star_dotProduct_diagonal_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    star_mulVec, conjTranspose_conjTranspose]

/-- Decomposes `star v ⬝ᵥ A *ᵥ v` into its diagonal squared-norm sum and its off-diagonal part
`star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v`. -/
theorem star_dotProduct_mulVec_eq_sum_diag_add (A : Matrix n n 𝕜) (v : n → 𝕜) :
    star v ⬝ᵥ A *ᵥ v =
      (∑ i, A i i * ((‖v i‖ ^ 2 : ℝ) : 𝕜)) + star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v := by
  nth_rw 1 [← add_sub_cancel (diagonal A.diag) A]
  simp only [add_mulVec, dotProduct_add, star_dotProduct_diagonal_mulVec, diag_apply]

omit [DecidableEq n] in
/-- Subtracting a weighted diagonal sum leaves the off-diagonal sum and the weighted
differences from the diagonal squared norms. -/
theorem star_dotProduct_mulVec_sub_sum_diag_eq (A : Matrix n n 𝕜) (v : n → 𝕜) (m : n → ℝ) :
    star v ⬝ᵥ A *ᵥ v - ∑ i, A i i * (m i : 𝕜) =
      (∑ p ∈ (Finset.univ : Finset n).offDiag, A p.1 p.2 * (star (v p.1) * v p.2)) +
      ∑ i, A i i * ((‖v i‖ ^ 2 - m i : ℝ) : 𝕜) := by
  classical
  rw [A.star_dotProduct_mulVec_eq_sum_diag_add,
    A.dotProduct_mulVec_sub_diagonal_eq_sum_offDiag, add_comm, add_sub_assoc,
    ← Finset.sum_sub_distrib]
  simp only [RCLike.ofReal_sub, mul_sub, Pi.star_apply, mul_assoc, mul_left_comm (star _) (A _ _)]

/-- Real part of the diagonal/off-diagonal decomposition of `star v ⬝ᵥ A *ᵥ v`. -/
theorem re_star_dotProduct_mulVec_eq_sum_diag_add (A : Matrix n n 𝕜) (v : n → 𝕜) :
    RCLike.re (star v ⬝ᵥ A *ᵥ v) =
      (∑ i, RCLike.re (A i i) * ‖v i‖ ^ 2) + RCLike.re (star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v) := by
  rw [A.star_dotProduct_mulVec_eq_sum_diag_add v, map_add, map_sum]
  simp [RCLike.mul_re]

omit [DecidableEq n] in
/-- **Polarization for Hermitian matrices.** A Hermitian matrix over `ℝ` or `ℂ` whose quadratic
form `star v ⬝ᵥ A *ᵥ v` vanishes identically is zero. -/
theorem IsHermitian.forall_star_dotProduct_mulVec_self_eq_zero_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : (∀ v, star v ⬝ᵥ A *ᵥ v = 0) ↔ A = 0 := by
  classical
  refine ⟨fun h => ?_, fun h v => by simp [h]⟩
  refine toEuclideanLin.injective ?_
  rw [map_zero, ← (isSymmetric_toEuclideanLin_iff.mpr hA).inner_map_self_eq_zero]
  intro x
  rw [inner_eq_zero_symm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simpa using h x

end Matrix
