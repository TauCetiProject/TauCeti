/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Realify
public import Mathlib.Analysis.Matrix.Order

/-!
# Positivity and norms of realified matrices

Realification preserves and reflects positive semidefiniteness. This allows Hermitian
covariance matrices to be used as real covariance matrices after splitting coordinates
into real and imaginary parts. The quadratic form of the realification is the real part
of the original Hermitian quadratic form. Positivity is transported using Mathlib's
`CStarAlgebra.nonneg_iff_eq_star_mul_self` and recovered from the quadratic form.

For an arbitrary `𝕜`-matrix `A`, we also record that `A.realify` has twice the squared Frobenius
norm (`Matrix.sum_sq_realify`) and the same Euclidean `ℓ²` operator norm
(`Matrix.l2_opNorm_realify`) as `A`.
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
        (isUnit_det_realify_iff.mpr ((isUnit_iff_isUnit_det A).mp hA.isUnit)))

/-- The sum of squared entries of `A.realify` is twice the sum of squared norms of the entries of
`A`. -/
theorem sum_sq_realify {m : Type*} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    (∑ p, ∑ q, A.realify p q ^ 2) = 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Fintype.sum_sum_type, realify_apply_inl_inl, realify_apply_inl_inr,
    realify_apply_inr_inl, realify_apply_inr_inr, neg_sq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hnorm : RCLike.re (A i j) ^ 2 + RCLike.im (A i j) ^ 2 = ‖A i j‖ ^ 2 := by
    rw [← RCLike.normSq_eq_def', RCLike.normSq_apply]
    ring
  linarith

private theorem norm_toLp_sumElim_re_im_sq {α : Type*} [Fintype α] (v : α → 𝕜) :
    ‖(WithLp.toLp 2 (Sum.elim (fun j ↦ RCLike.re (v j)) (fun j ↦ RCLike.im (v j))) :
        EuclideanSpace ℝ (α ⊕ α))‖ ^ 2 =
      ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 α)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs, sq_abs]
  rw [← RCLike.normSq_eq_def', RCLike.normSq_apply]
  ring

/-- Realification preserves the `ℓ²` operator norm of rectangular matrices. -/
@[simp]
theorem l2_opNorm_realify {m : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.realify‖ = ‖A‖ := by
  let TR := (toEuclideanLin (𝕜 := ℝ) (m := m ⊕ m) (n := n ⊕ n)).trans
    LinearMap.toContinuousLinearMap A.realify
  let TK := (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap A
  have hsplit (z : n → 𝕜) (i : m) :
      (A.realify *ᵥ Sum.elim (fun j ↦ RCLike.re (z j)) (fun j ↦ RCLike.im (z j))) (.inl i) =
        RCLike.re ((A *ᵥ z) i) ∧
      (A.realify *ᵥ Sum.elim (fun j ↦ RCLike.re (z j)) (fun j ↦ RCLike.im (z j))) (.inr i) =
        RCLike.im ((A *ᵥ z) i) := by
    constructor <;>
    · simp only [mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        realify_apply_inl_inl, realify_apply_inl_inr, realify_apply_inr_inl, realify_apply_inr_inr,
        neg_mul, Finset.sum_neg_distrib, map_sum, RCLike.mul_re, RCLike.mul_im,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
  refine le_antisymm ?_ ?_
  · refine TR.opNorm_le_bound (norm_nonneg A) fun w ↦ ?_
    obtain hI | hI := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
    · let w₁ : EuclideanSpace 𝕜 n := WithLp.toLp 2 fun j ↦ (w.ofLp (.inl j) : 𝕜)
      let w₂ : EuclideanSpace 𝕜 n := WithLp.toLp 2 fun j ↦ (w.ofLp (.inr j) : 𝕜)
      have hw_sq : ‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 = ‖w‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
          Fintype.sum_sum_type]
        simp [w₁, w₂, sq_abs]
      have hTR_sq : ‖TR w‖ ^ 2 = ‖TK w₁‖ ^ 2 + ‖TK w₂‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
          Fintype.sum_sum_type]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
        · have h1 : (TR w).ofLp (.inl i) = RCLike.re ((TK w₁).ofLp i) := by
            simp [TR, TK, w₁, toLpLin_apply, mulVec, dotProduct, Fintype.sum_sum_type,
              RCLike.im_eq_zero hI]
          have him : RCLike.im ((TK w₁).ofLp i) = 0 := RCLike.im_eq_zero hI _
          rw [h1, Real.norm_eq_abs, sq_abs, ← RCLike.normSq_eq_def', RCLike.normSq_apply, him]
          ring
        · have h2 : (TR w).ofLp (.inr i) = RCLike.re ((TK w₂).ofLp i) := by
            simp [TR, TK, w₂, toLpLin_apply, mulVec, dotProduct, Fintype.sum_sum_type,
              RCLike.im_eq_zero hI]
          have him : RCLike.im ((TK w₂).ofLp i) = 0 := RCLike.im_eq_zero hI _
          rw [h2, Real.norm_eq_abs, sq_abs, ← RCLike.normSq_eq_def', RCLike.normSq_apply, him]
          ring
      have hb₁ : ‖TK w₁‖ ^ 2 ≤ (‖A‖ * ‖w₁‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (TK.le_opNorm w₁) 2
      have hb₂ : ‖TK w₂‖ ^ 2 ≤ (‖A‖ * ‖w₂‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (TK.le_opNorm w₂) 2
      have hsq : ‖TR w‖ ^ 2 ≤ (‖A‖ * ‖w‖) ^ 2 := by
        calc ‖TR w‖ ^ 2 = ‖TK w₁‖ ^ 2 + ‖TK w₂‖ ^ 2 := hTR_sq
          _ ≤ (‖A‖ * ‖w₁‖) ^ 2 + (‖A‖ * ‖w₂‖) ^ 2 := add_le_add hb₁ hb₂
          _ = ‖A‖ ^ 2 * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) := by ring
          _ = (‖A‖ * ‖w‖) ^ 2 := by rw [hw_sq]; ring
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
    · let z : n → 𝕜 := fun j ↦ (w.ofLp (.inl j) : 𝕜) + (w.ofLp (.inr j) : 𝕜) * RCLike.I
      have hre (j : n) : RCLike.re (z j) = w.ofLp (.inl j) := by
        simp [z, RCLike.mul_re, RCLike.I_re]
      have him (j : n) : RCLike.im (z j) = w.ofLp (.inr j) := by
        simp [z, RCLike.mul_im, hI]
      have hw_eq : w = WithLp.toLp 2 (Sum.elim (fun j ↦ RCLike.re (z j))
          (fun j ↦ RCLike.im (z j))) := by
        ext p; rcases p with j | j <;> simp [hre, him]
      have hTRw : TR w = WithLp.toLp 2 (Sum.elim (fun i ↦ RCLike.re ((A *ᵥ z) i))
          (fun i ↦ RCLike.im ((A *ᵥ z) i))) := by
        ext p
        rcases p with i | i
        · simpa [TR, hw_eq, toLpLin_apply] using (hsplit z i).1
        · simpa [TR, hw_eq, toLpLin_apply] using (hsplit z i).2
      have h1 : ‖TR w‖ = ‖TK (WithLp.toLp 2 z)‖ := by
        refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
        simpa [TK, toLpLin_apply, hTRw] using norm_toLp_sumElim_re_im_sq (A *ᵥ z)
      have h2 : ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 n)‖ = ‖w‖ := by
        refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
        simpa [← hw_eq] using (norm_toLp_sumElim_re_im_sq z).symm
      rw [h1, ← h2]
      exact TK.le_opNorm (WithLp.toLp 2 z)
  · refine TK.opNorm_le_bound (norm_nonneg A.realify) fun z ↦ ?_
    let w : EuclideanSpace ℝ (n ⊕ n) :=
      WithLp.toLp 2 (Sum.elim (fun j ↦ RCLike.re (z.ofLp j)) (fun j ↦ RCLike.im (z.ofLp j)))
    have hTRw : TR w = WithLp.toLp 2 (Sum.elim (fun i ↦ RCLike.re ((A *ᵥ z.ofLp) i))
        (fun i ↦ RCLike.im ((A *ᵥ z.ofLp) i))) := by
      ext p
      rcases p with i | i
      · simpa [TR, w, toLpLin_apply] using (hsplit z.ofLp i).1
      · simpa [TR, w, toLpLin_apply] using (hsplit z.ofLp i).2
    have h1 : ‖TK z‖ = ‖TR w‖ := by
      refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      simpa [TK, toLpLin_apply, hTRw] using (norm_toLp_sumElim_re_im_sq (A *ᵥ z.ofLp)).symm
    have h2 : ‖w‖ = ‖z‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (norm_toLp_sumElim_re_im_sq z.ofLp)
    rw [h1, ← h2]
    exact TR.le_opNorm w

end Matrix
