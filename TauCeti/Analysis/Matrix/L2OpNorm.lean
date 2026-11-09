/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm

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

end Matrix
