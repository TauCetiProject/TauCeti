/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
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
* `Matrix.l2_opNorm_mul_conjTranspose_self`: the operator norm of `A * Aᴴ` is `‖A‖ * ‖A‖`.
* `Matrix.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq`: a Frobenius bound by the operator norm.
* `Matrix.l2_opNorm_sub_diagonal_diag_le`: zeroing the diagonal of a square matrix at most doubles
  its `ℓ²` operator norm.
* `Matrix.l2_opNorm_map_ofReal`: a real, possibly rectangular, matrix has the same `ℓ²` operator
  norm as a complex matrix.
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

/-- The Euclidean operator norm of `A * Aᴴ` is `‖A‖ * ‖A‖`, for a possibly rectangular `A`.
Mathlib's `Matrix.l2_opNorm_conjTranspose_mul_self` is the form for `Aᴴ * A`. -/
theorem l2_opNorm_mul_conjTranspose_self {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) : ‖A * Aᴴ‖ = ‖A‖ * ‖A‖ := by
  simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] using
    l2_opNorm_conjTranspose_mul_self Aᴴ

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
    _ = (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by rw [l2_opNorm_mul_conjTranspose_self, sq]

/-- The sum of squared entry norms over any set of positions is at most the row count times
the squared Euclidean operator norm. -/
theorem sum_norm_sq_le_card_mul_l2_opNorm_sq {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) (s : Finset (m × n)) :
    ∑ p ∈ s, ‖A p.1 p.2‖ ^ 2 ≤ (Fintype.card m : ℝ) * ‖A‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ p ∈ (Finset.univ : Finset m) ×ˢ (Finset.univ : Finset n), ‖A p.1 p.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ ↦ by simp) (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_product _ _ _
    _ ≤ _ := A.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq

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

section OfReal

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **A real matrix has the same `ℓ²` operator norm over `ℂ`**: its norm as an operator
`ℂⁿ → ℂᵐ` is its norm as an operator `ℝⁿ → ℝᵐ`. -/
@[simp]
theorem l2_opNorm_map_ofReal (S : Matrix m n ℝ) : ‖S.map ((↑) : ℝ → ℂ)‖ = ‖S‖ := by
  refine le_antisymm ?_ ?_
  · rw [l2_opNorm_def (S.map _)]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', toLpLin_apply]
    -- Split `v = a + i b` with real `a` and `b`: `‖S v‖² = ‖S a‖² + ‖S b‖²`.
    let a : EuclideanSpace ℝ n := WithLp.toLp 2 fun i ↦ (v i).re
    let b : EuclideanSpace ℝ n := WithLp.toLp 2 fun i ↦ (v i).im
    have ha : ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m)‖ ≤ ‖S‖ * ‖a‖ :=
      l2_opNorm_mulVec S a
    have hb : ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m)‖ ≤ ‖S‖ * ‖b‖ :=
      l2_opNorm_mulVec S b
    have hv : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, a, b, ← Finset.sum_add_distrib, Real.norm_eq_abs,
        sq_abs, Complex.sq_norm, Complex.normSq_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hSv : ‖(WithLp.toLp 2 (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp v) : EuclideanSpace ℂ m)‖ ^ 2 =
        ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m)‖ ^ 2 +
          ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m)‖ ^ 2 := by
      have hcoord (i : m) :
          (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp v) i = ∑ j, (S i j : ℂ) * v j := by
        simp [mulVec, dotProduct]
      simp only [EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib, Real.norm_eq_abs,
        sq_abs, Complex.sq_norm, Complex.normSq_apply, hcoord]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hre : (∑ j, ((S i j : ℂ) * v j)).re = (S *ᵥ WithLp.ofLp a) i := by
        simp [mulVec, dotProduct, Complex.re_sum, a]
      have him : (∑ j, ((S i j : ℂ) * v j)).im = (S *ᵥ WithLp.ofLp b) i := by
        simp [mulVec, dotProduct, Complex.im_sum, b]
      rw [hre, him]
      ring
    have h0 := norm_nonneg S
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hSv, mul_pow, hv]
    nlinarith [norm_nonneg (WithLp.toLp 2 (S *ᵥ WithLp.ofLp a) : EuclideanSpace ℝ m),
      norm_nonneg (WithLp.toLp 2 (S *ᵥ WithLp.ofLp b) : EuclideanSpace ℝ m),
      mul_nonneg h0 (norm_nonneg a), mul_nonneg h0 (norm_nonneg b)]
  · rw [l2_opNorm_def S]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', toLpLin_apply]
    -- A real vector has the same norm as a complex vector.
    let xc : EuclideanSpace ℂ n := WithLp.toLp 2 fun i ↦ (x i : ℂ)
    have hx : ‖xc‖ = ‖x‖ := by
      simp [EuclideanSpace.norm_eq, xc, Complex.norm_real]
    have hSx : ‖(WithLp.toLp 2 (S.map ((↑) : ℝ → ℂ) *ᵥ WithLp.ofLp xc) : EuclideanSpace ℂ m)‖ =
        ‖(WithLp.toLp 2 (S *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ m)‖ := by
      simp [EuclideanSpace.norm_eq, xc, mulVec, dotProduct, ← Complex.ofReal_mul,
        ← Complex.ofReal_sum]
    rw [← hSx, ← hx]
    exact l2_opNorm_mulVec _ xc
end OfReal

end Matrix
