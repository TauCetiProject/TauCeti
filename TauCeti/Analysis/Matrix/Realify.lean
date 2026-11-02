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

/-- Realification preserves and reflects positive definiteness. -/
@[simp]
theorem posDef_realify_iff [Finite n] {A : Matrix n n 𝕜} :
    A.realify.PosDef ↔ A.PosDef := by
  classical
  let _ := Fintype.ofFinite n
  constructor
  · intro hR
    have hA : A.PosSemidef := posSemidef_realify_iff.mp hR.posSemidef
    refine PosDef.of_dotProduct_mulVec_pos hA.isHermitian fun z hz ↦ ?_
    rw [RCLike.pos_iff]
    refine ⟨?_, RCLike.conj_eq_iff_im.mp (hA.isHermitian.star_dotProduct_mulVec_comm z z)⟩
    let y : n ⊕ n → ℝ :=
      Sum.elim (fun i ↦ RCLike.re (z i)) (fun i ↦ RCLike.im (z i))
    have hy : y ≠ 0 := by
      intro hy
      apply hz
      funext i
      apply RCLike.ext
      · simpa [y] using congr_fun hy (Sum.inl i)
      · simpa [y] using congr_fun hy (Sum.inr i)
    rw [← dotProduct_realify_mulVec]
    exact hR.dotProduct_mulVec_pos hy
  · intro hA
    have hR : A.realify.PosSemidef := posSemidef_realify_iff.mpr hA.posSemidef
    exact hR.posDef_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det A.realify).mpr
        (isUnit_det_realify ((isUnit_iff_isUnit_det A).mp hA.isUnit)))

end Matrix
