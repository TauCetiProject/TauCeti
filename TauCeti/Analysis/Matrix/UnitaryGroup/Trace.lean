/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.Matrix.Frobenius

/-!
# The trace of a unitary matrix

The entries of a unitary matrix `U` over `ℝ` or `ℂ` have norm at most one
(`entry_norm_bound_of_unitary`), so `‖tr (U - 1)‖ ≤ 2 · card n`. The trace also detects the
identity: `‖U - 1‖² = re tr ((U - 1)(U - 1)ᴴ) = 2 · card n - 2 · re tr U` for the Frobenius norm,
so `U = 1` as soon as `re tr U = card n`.

## Main results

* `Matrix.norm_trace_sub_one_le_of_mem_unitaryGroup`: `‖tr (U - 1)‖ ≤ 2 · card n`.
* `Matrix.eq_one_of_re_trace_eq_card`: a unitary matrix whose trace has real part `card n` is
  the identity.
-/

public section

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The trace of `U - 1`, for a unitary matrix `U` over `ℝ` or `ℂ`, has norm at most
`2 · card n`, since every diagonal entry of `U` has norm at most one. -/
theorem norm_trace_sub_one_le_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖(U - 1).trace‖ ≤ 2 * Fintype.card n := by
  calc ‖(U - 1).trace‖ ≤ ∑ i, ‖(U - 1) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        simp only [Matrix.sub_apply, Matrix.one_apply_eq]
        linarith [norm_sub_le (U i i) 1, norm_one (α := 𝕜), entry_norm_bound_of_unitary hU i i]
    _ = 2 * Fintype.card n := by simp [mul_comm]

/-- A unitary matrix over `ℝ` or `ℂ` whose trace has real part `card n` is the identity: the
squared Frobenius norm of `U - 1` is `2 · card n - 2 · re tr U`. -/
theorem eq_one_of_re_trace_eq_card {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (h : RCLike.re U.trace = Fintype.card n) : U = 1 := by
  have hU' : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  have key : (U - 1) * (U - 1)ᴴ = 1 + 1 - U - Uᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, mul_sub, sub_mul, hU', Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [← sub_eq_zero, ← re_trace_mul_conjTranspose_self_eq_zero_iff, key]
  simp [trace_conjTranspose, h]

end Matrix
