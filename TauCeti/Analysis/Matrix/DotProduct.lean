/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Diagonal and off-diagonal decomposition of `RCLike` matrix quadratic forms

For a square matrix `A : Matrix n n 𝕜` over an `RCLike` field `𝕜`, the sesquilinear quadratic form
`star v ⬝ᵥ A *ᵥ v` splits into the weighted squared-norm sum `∑ i, A i i * ‖v i‖ ^ 2` and the
off-diagonal form `star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v`
(`Matrix.star_dotProduct_mulVec_eq_sum_diag_add`), with real-part counterpart
`Matrix.re_star_dotProduct_mulVec_eq_sum_diag_add`.

A Hermitian matrix is determined by its quadratic form: if `star v ⬝ᵥ A *ᵥ v = 0` for every `v`,
then `A = 0` (`Matrix.IsHermitian.forall_star_dotProduct_mulVec_self_eq_zero_iff`). This is
polarization for Hermitian forms, read from Mathlib's
`LinearMap.IsSymmetric.inner_map_self_eq_zero` through `Matrix.toEuclideanLin`.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

section

variable [CommRing 𝕜] [Star 𝕜]

/-- The zero-diagonal part of a quadratic form is its sum over ordered off-diagonal pairs. -/
theorem star_dotProduct_mulVec_sub_diagonal_eq_sum_offDiag (A : Matrix n n 𝕜) (v : n → 𝕜) :
    star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v =
      ∑ p ∈ (Finset.univ : Finset n).offDiag, A p.1 p.2 * (star (v p.1) * v p.2) := by
  let f (p : n × n) := (A - diagonal A.diag) p.1 p.2 * (star (v p.1) * v p.2)
  have he : star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v =
      ∑ p ∈ (Finset.univ : Finset n) ×ˢ (Finset.univ : Finset n), f p := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm, Finset.sum_product]
    simp only [Pi.star_apply, f]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ac_rfl
  rw [he, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _),
    Finset.sum_diag]
  simp only [f, Matrix.sub_apply, diagonal_apply_eq, diag_apply, sub_self, zero_mul,
    Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun _ hp ↦ by
    rw [diagonal_apply_ne _ (Finset.mem_offDiag.mp hp).2.2, sub_zero]

end

variable [RCLike 𝕜]

/-- Decomposes `star v ⬝ᵥ A *ᵥ v` into its diagonal squared-norm sum and its off-diagonal part
`star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v`. -/
theorem star_dotProduct_mulVec_eq_sum_diag_add (A : Matrix n n 𝕜) (v : n → 𝕜) :
    star v ⬝ᵥ A *ᵥ v =
      (∑ i, A i i * ((‖v i‖ ^ 2 : ℝ) : 𝕜)) + star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v := by
  have hdiag : star v ⬝ᵥ diagonal A.diag *ᵥ v = ∑ i, A i i * ((‖v i‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [dotProduct, mulVec_diagonal, diag_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm, RCLike.star_def, RCLike.conj_mul]; norm_cast
  nth_rw 1 [← add_sub_cancel (diagonal A.diag) A]
  rw [add_mulVec, dotProduct_add, hdiag]

omit [DecidableEq n] in
/-- Subtracting a weighted diagonal sum leaves the off-diagonal sum and the weighted
differences from the diagonal squared norms. -/
theorem star_dotProduct_mulVec_sub_sum_diag_eq (A : Matrix n n 𝕜) (v : n → 𝕜) (m : n → ℝ) :
    star v ⬝ᵥ A *ᵥ v - ∑ i, A i i * (m i : 𝕜) =
      (∑ p ∈ (Finset.univ : Finset n).offDiag, A p.1 p.2 * (star (v p.1) * v p.2)) +
      ∑ i, A i i * ((‖v i‖ ^ 2 - m i : ℝ) : 𝕜) := by
  classical
  rw [A.star_dotProduct_mulVec_eq_sum_diag_add,
    A.star_dotProduct_mulVec_sub_diagonal_eq_sum_offDiag, add_comm, add_sub_assoc,
    ← Finset.sum_sub_distrib]
  simp only [RCLike.ofReal_sub, mul_sub]

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
