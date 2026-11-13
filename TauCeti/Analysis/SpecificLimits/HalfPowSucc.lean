/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Partial sums of the weights `2⁻⁽ʳ⁺¹⁾`

The weights `(1 / 2) ^ (r + 1)` have partial sums at most `1`, the normalisation needed to
distribute a total tolerance over a sequence of stages.

## Main results

* `TauCeti.sum_half_pow_succ_le_one`: the partial sums are at most `1`.
-/

public section

namespace TauCeti

/-- The weights `2⁻⁽ʳ⁺¹⁾` sum to at most `1`. -/
theorem sum_half_pow_succ_le_one (N : ℕ) :
    ∑ r ∈ Finset.range N, (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := by
  have h := sum_geometric_two_le N
  have hw' : ∑ r ∈ Finset.range N, (1 / 2 : ℝ) ^ (r + 1) =
      1 / 2 * ∑ r ∈ Finset.range N, (1 / 2 : ℝ) ^ r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ ↦ pow_succ' _ _
  linarith

end TauCeti
