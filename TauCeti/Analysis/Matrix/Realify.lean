/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Realify
public import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of realified matrices

Realification preserves and reflects positive semidefiniteness. This allows Hermitian
covariance matrices to be used as real covariance matrices after splitting coordinates
into real and imaginary parts. The quadratic form of the realification is the real part
of the original Hermitian quadratic form. Positivity is transported using Mathlib's
`CStarAlgebra.nonneg_iff_eq_star_mul_self` and recovered from the quadratic form.
-/

public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- The quadratic form of a realified matrix is the real part of its original quadratic
form, evaluated at the split real and imaginary coordinates. -/
theorem dotProduct_realify_mulVec [Fintype n] (A : Matrix n n 𝕜) (z : n → 𝕜) :
    Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i)) ⬝ᵥ
        A.realify *ᵥ Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i)) =
      RCLike.re (star z ⬝ᵥ A *ᵥ z) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, RCLike.mul_re, RCLike.mul_im,
    Sum.elim_inl, Sum.elim_inr, realify_apply_inl_inl, realify_apply_inl_inr,
    realify_apply_inr_inl, realify_apply_inr_inr, Pi.star_apply, map_sum,
    RCLike.star_def, RCLike.conj_re, RCLike.conj_im]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Realification preserves and reflects positive semidefiniteness. -/
@[simp]
theorem posSemidef_realify_iff [Finite n] {A : Matrix n n 𝕜} :
    A.realify.PosSemidef ↔ A.PosSemidef := by
  classical
  let : Fintype n := Fintype.ofFinite n
  constructor
  · intro h
    have hA : A.IsHermitian := by
      apply realify_injective
      rw [realify_conjTranspose, ← conjTranspose_eq_transpose_of_trivial, h.isHermitian.eq]
    refine .of_dotProduct_mulVec_nonneg hA fun z ↦ ?_
    rw [RCLike.nonneg_iff]
    refine ⟨?_, ?_⟩
    · rw [← dotProduct_realify_mulVec]
      simpa using h.dotProduct_mulVec_nonneg
        (Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i)))
    · exact RCLike.conj_eq_iff_im.mp (hA.star_dotProduct_mulVec_comm z z)
  · intro h
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
    rw [hB, star_eq_conjTranspose, realify_mul, realify_conjTranspose,
      ← conjTranspose_eq_transpose_of_trivial]
    exact posSemidef_conjTranspose_mul_self _

end Matrix
