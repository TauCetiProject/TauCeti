/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# The Neumann series of a discounted row-stochastic matrix

The rows of a real row-stochastic matrix `P` are probability vectors, so `P` has norm at most `1`
for the `L∞` operator norm, the largest absolute row sum
(`Matrix.linfty_opNorm_le_one_of_mem_rowStochastic`). For a discount `0 ≤ c < 1`, and more
generally for `|c| < 1`, the matrix `c • P` therefore has norm below `1`, and its Neumann series
converges to the inverse of `1 - c • P`: `∑ₖ (c • P) ^ k = Ring.inverse (1 - c • P)`
(`Matrix.hasSum_pow_smul_of_mem_rowStochastic`), in the entrywise topology of matrices, which
the operator norm induces.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Appendix C.
-/

public section

open scoped NNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
/-- A real row-stochastic matrix has `L∞` operator norm at most `1`: each of its absolute row sums
is `1`. -/
theorem linfty_opNorm_le_one_of_mem_rowStochastic {P : Matrix n n ℝ}
    (hP : P ∈ rowStochastic ℝ n) : ‖P‖ ≤ 1 := by
  rw [linfty_opNorm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ ↦ NNReal.coe_le_coe.1 ?_
  push_cast
  simp only [Real.norm_eq_abs, abs_of_nonneg (nonneg_of_mem_rowStochastic hP),
    sum_row_of_mem_rowStochastic hP, le_refl]

/-- **The Neumann series of a discounted row-stochastic matrix.** For a real row-stochastic matrix
`P` and `|c| < 1`, the powers of `c • P` sum to `Ring.inverse (1 - c • P)`. -/
theorem hasSum_pow_smul_of_mem_rowStochastic {P : Matrix n n ℝ}
    (hP : P ∈ rowStochastic ℝ n) {c : ℝ} (hc : |c| < 1) :
    HasSum (fun k ↦ (c • P) ^ k) (Ring.inverse (1 - c • P)) := by
  open scoped Matrix.Norms.Operator in
  refine hasSum_geom_series_inverse _ ((norm_smul_le c P).trans_lt ?_)
  open scoped Matrix.Norms.Operator in
  calc ‖c‖ * ‖P‖ ≤ ‖c‖ * 1 :=
        mul_le_mul_of_nonneg_left (linfty_opNorm_le_one_of_mem_rowStochastic hP) (norm_nonneg c)
    _ < 1 := by rwa [mul_one, Real.norm_eq_abs]

end Matrix
