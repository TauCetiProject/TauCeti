/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Norm
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
import TauCeti.Analysis.Matrix.Frobenius

/-!
# The `ℓ²` operator norm as a normed real algebra

Mathlib's scoped `ℓ²` operator norm (`Matrix.Norms.L2Operator`) makes `Matrix n n 𝕜` a normed
`𝕜`-algebra, for `𝕜 = ℝ` or `ℂ` (any `RCLike` field). Results about continuous functional
calculi and the exponential stated over `ℝ` additionally need a normed `ℝ`-algebra structure on
`Matrix n n 𝕜`. This file provides it, extending the existing `ℝ`-algebra structure on matrices
rather than restricting scalars, so that no algebra diamond arises.

## Main definitions

* `Matrix.l2OpNormedAlgebraReal`: `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed
  `ℝ`-algebra.

## Main results

* `Matrix.norm_apply_le_l2_opNorm`: an entrywise bound, including rectangular matrices.
* `Matrix.l2_opNorm_one_le`: an identity bound that also applies to empty matrices.
* `Matrix.norm_trace_le_card_mul_l2_opNorm` and `Matrix.norm_normalized_trace_le_l2_opNorm`:
  trace and normalized trace bounds.
* `Matrix.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq`: a Frobenius bound by the operator norm.
* `Matrix.l2_opNorm_sub_diagonal_diag_le`: zeroing the diagonal of a square matrix at most doubles
  its `ℓ²` operator norm.
* `Matrix.l2_opNorm_fromBlocks_diagonal`: the `ℓ²` operator norm of a block-diagonal matrix
  `fromBlocks A 0 0 B` is `max ‖A‖ ‖B‖`.
* `Matrix.l2_opNorm_fromBlocks_zero_conjTranspose`: the Hermitian dilation `fromBlocks 0 A Aᴴ 0`
  has the same `ℓ²` operator norm as `A`.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- Every entry is bounded by the Euclidean operator norm. -/
theorem norm_apply_le_l2_opNorm {m : Type*} [Fintype m] (A : Matrix m n 𝕜)
    (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace 𝕜 n := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  let v : EuclideanSpace 𝕜 m := (EuclideanSpace.equiv m 𝕜).symm (A *ᵥ e)
  have h := PiLp.norm_apply_le v i
  have hi : v.ofLp i = A i j := by
    simp [v, e, Matrix.mulVec_single]
  rw [hi] at h
  exact h.trans (by simpa [v, he] using A.l2_opNorm_mulVec e)

/-- The norm of the identity is at most one, also when the index type is empty. -/
theorem l2_opNorm_one_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by simp)

/-- The trace is bounded by the dimension times the Euclidean operator norm. -/
theorem norm_trace_le_card_mul_l2_opNorm (M : Matrix n n 𝕜) :
    ‖M.trace‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  have h := ContinuousLinearMap.norm_traceCLM_le
    (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) M)
  simpa only [TauCeti.traceCLM_apply, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.coe_coe,
    Matrix.trace_toLin_eq, finrank_euclideanSpace, Matrix.l2_opNorm_toEuclideanCLM] using h

/-- The squared Frobenius norm of a rectangular matrix is at most its number of rows times
its squared Euclidean operator norm. Empty row and column types are allowed. -/
theorem sum_sum_norm_sq_le_card_mul_l2_opNorm_sq {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by
  classical
  calc
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = RCLike.re (A * Aᴴ).trace :=
      (re_trace_mul_conjTranspose_self A).symm
    _ ≤ ‖(A * Aᴴ).trace‖ := RCLike.re_le_norm _
    _ ≤ (Fintype.card m : ℝ) * ‖A * Aᴴ‖ := norm_trace_le_card_mul_l2_opNorm _
    _ = (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by
      have h := l2_opNorm_conjTranspose_mul_self Aᴴ
      simp only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] at h
      rw [h, sq]

/-- The absolute normalized trace is at most the Euclidean operator norm, including in dimension
zero. -/
theorem norm_normalized_trace_le_l2_opNorm (M : Matrix n n 𝕜) :
    ‖((Fintype.card n : ℕ) : 𝕜)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  by_cases hn : Nonempty n
  · let : Nonempty n := hn
    have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    rw [norm_mul, norm_inv, RCLike.norm_natCast]
    exact (inv_mul_le_iff₀ hcard).2 (norm_trace_le_card_mul_l2_opNorm M)
  · have : IsEmpty n := not_nonempty_iff.mp hn
    simp

open scoped Matrix.Norms.L2Operator in
/-- `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed `ℝ`-algebra. It extends the existing
`ℝ`-algebra structure rather than restricting scalars, so that no algebra diamond arises. -/
protected noncomputable abbrev l2OpNormedAlgebraReal : NormedAlgebra ℝ (Matrix n n 𝕜) where
  __ := (inferInstance : Algebra ℝ (Matrix n n 𝕜))
  norm_smul_le r A := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])

/-- Removing the diagonal of a square matrix increases its `ℓ²` operator norm by at most a factor
of `2`. -/
theorem l2_opNorm_sub_diagonal_diag_le (A : Matrix n n 𝕜) :
    ‖A - diagonal A.diag‖ ≤ 2 * ‖A‖ := by
  have hdiag : ‖(diagonal A.diag : Matrix n n 𝕜)‖ ≤ ‖A‖ := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr fun i ↦ A.norm_apply_le_l2_opNorm i i
  linarith [norm_sub_le A (diagonal A.diag)]

/-- Canonical linear isometry equivalence identifying `EuclideanSpace 𝕜 (m ⊕ p)` with the `L²`
direct sum `WithLp 2 (EuclideanSpace 𝕜 m × EuclideanSpace 𝕜 p)`. -/
private noncomputable def euclideanSpaceSumEquiv (𝕜 m p : Type*) [RCLike 𝕜]
    [Fintype m] [Fintype p] :
    EuclideanSpace 𝕜 (m ⊕ p) ≃ₗᵢ[𝕜] WithLp 2 (EuclideanSpace 𝕜 m × EuclideanSpace 𝕜 p) where
  toFun x := WithLp.toLp 2 (WithLp.toLp 2 (x.ofLp ∘ Sum.inl), WithLp.toLp 2 (x.ofLp ∘ Sum.inr))
  invFun z := WithLp.toLp 2 (Sum.elim z.fst.ofLp z.snd.ofLp)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext <;> rfl
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext <;> rfl
  left_inv x := by
    apply WithLp.ofLp_injective 2
    ext k
    cases k <;> rfl
  right_inv z := by
    apply WithLp.ofLp_injective 2
    ext <;> rfl
  norm_map' x := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
    rfl

private theorem euclideanSpaceSumEquiv_apply (𝕜 m p : Type*) [RCLike 𝕜]
    [Fintype m] [Fintype p] (x : EuclideanSpace 𝕜 (m ⊕ p)) :
    euclideanSpaceSumEquiv 𝕜 m p x =
      WithLp.toLp 2 (WithLp.toLp 2 (x.ofLp ∘ Sum.inl), WithLp.toLp 2 (x.ofLp ∘ Sum.inr)) :=
  rfl

private theorem euclideanSpaceSumEquiv_symm_apply (𝕜 m p : Type*) [RCLike 𝕜]
    [Fintype m] [Fintype p] (z : WithLp 2 (EuclideanSpace 𝕜 m × EuclideanSpace 𝕜 p)) :
    (euclideanSpaceSumEquiv 𝕜 m p).symm z = WithLp.toLp 2 (Sum.elim z.fst.ofLp z.snd.ofLp) :=
  rfl

/-- The `ℓ²` operator norm of a block-diagonal rectangular matrix is the maximum of the `ℓ²`
operator norms of its diagonal blocks. -/
theorem l2_opNorm_fromBlocks_diagonal {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]
    (A : Matrix m₁ n₁ 𝕜) (B : Matrix m₂ n₂ 𝕜) :
    ‖fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ := by
  let eOut := euclideanSpaceSumEquiv 𝕜 m₁ m₂
  let eIn := euclideanSpaceSumEquiv 𝕜 n₁ n₂
  apply le_antisymm
  · rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg A)) fun x ↦ ?_
    let u : EuclideanSpace 𝕜 n₁ := WithLp.toLp 2 (x.ofLp ∘ Sum.inl)
    let v : EuclideanSpace 𝕜 n₂ := WithLp.toLp 2 (x.ofLp ∘ Sum.inr)
    have hmul : (fromBlocks A 0 0 B) *ᵥ x.ofLp = Sum.elim (A *ᵥ u.ofLp) (B *ᵥ v.ofLp) := by
      have hx : x.ofLp = Sum.elim u.ofLp v.ofLp := by
        ext k; cases k <;> rfl
      rw [hx, fromBlocks_mulVec]
      simp [u, v]
    have hnorm_out : ‖((toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (fromBlocks A 0 0 B)) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv m₁ 𝕜).symm (A *ᵥ u.ofLp)‖ ^ 2 +
          ‖(EuclideanSpace.equiv m₂ 𝕜).symm (B *ᵥ v.ofLp)‖ ^ 2 := by
      have h1 := congrArg (· ^ 2)
        (eOut.norm_map (((toEuclideanLin.trans LinearMap.toContinuousLinearMap)
          (fromBlocks A 0 0 B)) x)).symm
      rw [WithLp.prod_norm_sq_eq_of_L2] at h1
      simpa [eOut, euclideanSpaceSumEquiv_apply, toLpLin_apply, hmul, EuclideanSpace.equiv] using h1
    have hnorm_in : ‖x‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      have h1 := congrArg (· ^ 2) (eIn.norm_map x).symm
      rw [WithLp.prod_norm_sq_eq_of_L2] at h1
      simpa only [eIn, euclideanSpaceSumEquiv_apply, WithLp.toLp_fst, WithLp.toLp_snd, u, v] using
        h1
    have hA : ‖(EuclideanSpace.equiv m₁ 𝕜).symm (A *ᵥ u.ofLp)‖ ≤ max ‖A‖ ‖B‖ * ‖u‖ :=
      (A.l2_opNorm_mulVec u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hB : ‖(EuclideanSpace.equiv m₂ 𝕜).symm (B *ᵥ v.ofLp)‖ ≤ max ‖A‖ ‖B‖ * ‖v‖ :=
      (B.l2_opNorm_mulVec v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hAsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_max_of_le_left (norm_nonneg A))
      (norm_nonneg _))).2 hA
    have hBsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_max_of_le_left (norm_nonneg A))
      (norm_nonneg _))).2 hB
    refine (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (le_max_of_le_left (norm_nonneg A)) (norm_nonneg _))).1 ?_
    rw [hnorm_out, mul_pow, hnorm_in]
    nlinarith [mul_pow (max ‖A‖ ‖B‖) ‖u‖ 2, mul_pow (max ‖A‖ ‖B‖) ‖v‖ 2]
  · refine max_le ?_ ?_
    · rw [l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
      let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := eIn.symm (WithLp.toLp 2 (u, (0 : EuclideanSpace 𝕜 n₂)))
      have hx_norm : ‖x‖ = ‖u‖ := by
        simp [x, WithLp.norm_toLp_fst]
      have hmul : (fromBlocks A 0 0 B) *ᵥ x.ofLp = Sum.elim (A *ᵥ u.ofLp) (0 : m₂ → 𝕜) := by
        simp [x, eIn, euclideanSpaceSumEquiv_symm_apply, fromBlocks_mulVec]
      have hout : ‖(EuclideanSpace.equiv (m₁ ⊕ m₂) 𝕜).symm ((fromBlocks A 0 0 B) *ᵥ x.ofLp)‖ =
          ‖(EuclideanSpace.equiv m₁ 𝕜).symm (A *ᵥ u.ofLp)‖ := by
        rw [← eOut.norm_map]
        simp [eOut, euclideanSpaceSumEquiv_apply, hmul]
      have hle := (fromBlocks A 0 0 B).l2_opNorm_mulVec x
      rw [hout, hx_norm] at hle
      exact hle
    · rw [l2_opNorm_def]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
      let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := eIn.symm (WithLp.toLp 2 ((0 : EuclideanSpace 𝕜 n₁), v))
      have hx_norm : ‖x‖ = ‖v‖ := by
        simp [x, WithLp.norm_toLp_snd]
      have hmul : (fromBlocks A 0 0 B) *ᵥ x.ofLp = Sum.elim (0 : m₁ → 𝕜) (B *ᵥ v.ofLp) := by
        simp [x, eIn, euclideanSpaceSumEquiv_symm_apply, fromBlocks_mulVec]
      have hout : ‖(EuclideanSpace.equiv (m₁ ⊕ m₂) 𝕜).symm ((fromBlocks A 0 0 B) *ᵥ x.ofLp)‖ =
          ‖(EuclideanSpace.equiv m₂ 𝕜).symm (B *ᵥ v.ofLp)‖ := by
        rw [← eOut.norm_map]
        simp [eOut, euclideanSpaceSumEquiv_apply, hmul]
      have hle := (fromBlocks A 0 0 B).l2_opNorm_mulVec x
      rw [hout, hx_norm] at hle
      exact hle

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular matrix `A` has the same `ℓ²`
operator norm as `A`. -/
theorem l2_opNorm_fromBlocks_zero_conjTranspose {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m p 𝕜) :
    ‖fromBlocks (0 : Matrix m m 𝕜) A Aᴴ 0‖ = ‖A‖ := by
  let e := euclideanSpaceSumEquiv 𝕜 m p
  let D : Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fromBlocks 0 A Aᴴ 0
  have hconj :
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Matrix.toEuclideanCLM (𝕜 := 𝕜) D).comp
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap) =
      (Aᴴ.toEuclideanLin).hermitianDilation.toContinuousLinearMap := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      LinearMap.hermitianDilation_apply, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_conjTranspose]
    simp [D, e, euclideanSpaceSumEquiv_apply, euclideanSpaceSumEquiv_symm_apply,
      toLpLin_apply, fromBlocks_mulVec]
  calc
    ‖D‖ = ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) D‖ := (l2_opNorm_toEuclideanCLM D).symm
    _ = ‖e.toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((Matrix.toEuclideanCLM (𝕜 := 𝕜) D).comp
            e.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ := by
        rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
          ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
    _ = ‖(Aᴴ.toEuclideanLin).hermitianDilation.toContinuousLinearMap‖ := by rw [hconj]
    _ = ‖Aᴴ.toEuclideanLin.toContinuousLinearMap‖ :=
        LinearMap.norm_toContinuousLinearMap_hermitianDilation Aᴴ.toEuclideanLin
    _ = ‖Aᴴ‖ := rfl
    _ = ‖A‖ := l2_opNorm_conjTranspose A

end Matrix
