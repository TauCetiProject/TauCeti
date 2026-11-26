/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import TauCeti.Combinatorics.Young.HookLength.Basic

/-!
# A logarithmic lower bound for the hook product

For a Young diagram `μ` with row lengths `μ_i = μ.rowLen i`, the factorials `μ_i!` multiply to at
most the product of the hook lengths (`YoungDiagram.prod_factorial_rowLen_le_prod_hookLength`).
Taking real logarithms, with `n log n - n ≤ log n!` (Mathlib's `Real.le_sum_log_nat`), gives
`∑_i (μ_i log μ_i - μ_i) ≤ log ∏_{c ∈ μ} hookLength μ c`.

The sum runs over `Finset.range N` for an arbitrary `N`: the rows from `μ.colLen 0` on are empty
and contribute `0 * log 0 - 0 = 0`, so `N = μ.colLen 0` gives the sum over all rows, and a smaller
`N` a part of it.

## Main results

* `YoungDiagram.sum_mul_log_sub_le_log_prod_hookLength`:
  `∑_{i < N} (μ_i log μ_i - μ_i) ≤ log ∏_{c ∈ μ} hookLength μ c`.

## References

* J. S. Frame, G. de B. Robinson and R. M. Thrall, *The hook graphs of the symmetric group*,
  Canad. J. Math. 6 (1954), where hook lengths are introduced.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, for hook lengths and the
  hook-length formula.
-/

public section

namespace YoungDiagram

/-- With `μ_i = μ.rowLen i`, the real numbers `μ_i log μ_i - μ_i` of the rows `i < N` sum to at
most the real logarithm of the product of all the hook lengths of `μ`, for any `N`. -/
theorem sum_mul_log_sub_le_log_prod_hookLength (μ : YoungDiagram) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((μ.rowLen i : ℝ) * Real.log (μ.rowLen i) - μ.rowLen i) ≤
      Real.log (∏ c ∈ μ.cells, (hookLength μ c : ℝ)) := by
  calc ∑ i ∈ Finset.range N, ((μ.rowLen i : ℝ) * Real.log (μ.rowLen i) - μ.rowLen i)
      ≤ ∑ i ∈ Finset.range N, Real.log ((μ.rowLen i).factorial : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          (Real.le_sum_log_nat _).trans_eq (Real.sum_log_eq_log_factorial _)
    _ = Real.log (∏ i ∈ Finset.range N, ((μ.rowLen i).factorial : ℝ)) :=
        (Real.log_prod fun i _ => by positivity).symm
    _ ≤ Real.log (∏ c ∈ μ.cells, (hookLength μ c : ℝ)) := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast μ.prod_factorial_rowLen_le_prod_hookLength N

end YoungDiagram
