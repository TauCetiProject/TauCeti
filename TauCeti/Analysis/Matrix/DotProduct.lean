/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Diagonal and off-diagonal decomposition of `RCLike` matrix quadratic forms

For a square matrix `A : Matrix n n 𝕜` over an `RCLike` field `𝕜`, the sesquilinear quadratic form
`star v ⬝ᵥ A *ᵥ v` splits into the weighted squared-norm sum `∑ i, A i i * ‖v i‖ ^ 2` and the
off-diagonal form `star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v`
(`Matrix.star_dotProduct_mulVec_eq_sum_diag_add`), with real-part counterpart
`Matrix.re_star_dotProduct_mulVec_eq_sum_diag_add`.

A Hermitian matrix is determined by its quadratic form: if `star x ⬝ᵥ A *ᵥ x` vanishes for every
`x`, then `A = 0` (`Matrix.IsHermitian.eq_zero_of_forall_star_dotProduct_mulVec_self`).
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

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

/-- Real part of the diagonal/off-diagonal decomposition of `star v ⬝ᵥ A *ᵥ v`. -/
theorem re_star_dotProduct_mulVec_eq_sum_diag_add (A : Matrix n n 𝕜) (v : n → 𝕜) :
    RCLike.re (star v ⬝ᵥ A *ᵥ v) =
      (∑ i, RCLike.re (A i i) * ‖v i‖ ^ 2) + RCLike.re (star v ⬝ᵥ (A - diagonal A.diag) *ᵥ v) := by
  rw [A.star_dotProduct_mulVec_eq_sum_diag_add v, map_add, map_sum]
  simp [RCLike.mul_re]

omit [DecidableEq n] in
/-- **Polarization for Hermitian matrices.** Over an `RCLike` field, a Hermitian matrix whose
quadratic form `x ↦ star x ⬝ᵥ (A *ᵥ x)` vanishes is zero. -/
theorem IsHermitian.eq_zero_of_forall_star_dotProduct_mulVec_self {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ x : n → 𝕜, star x ⬝ᵥ (A *ᵥ x) = 0) : A = 0 := by
  classical
  have hT := (isSymmetric_toEuclideanLin_iff.mpr hA).inner_map_self_eq_zero.mp fun x => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_dotProduct]
    simpa using congrArg star (h (WithLp.ofLp x))
  exact toEuclideanLin.injective (by rw [hT, map_zero])

end Matrix
