/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Partial sums of the weights `2⁻⁽ʳ⁺¹⁾`

The weights `(1 / 2) ^ (r + 1)` sum to `1`, and their partial sums are at most `1`: the
normalisation needed to distribute a total tolerance, or a unit mass, over a sequence of stages.
The tail from index `n` on sums to `(1 / 2) ^ n`.

## Main results

* `TauCeti.hasSum_half_pow_succ`: the weights sum to `1`.
* `TauCeti.tsum_half_pow_add_succ`: the tail from index `n` on sums to `(1 / 2) ^ n`.
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

/-- The weights `2⁻⁽ʳ⁺¹⁾` sum to one. -/
theorem hasSum_half_pow_succ : HasSum (fun r : ℕ ↦ (1 / 2 : ℝ) ^ (r + 1)) 1 := by
  convert hasSum_geometric_two' 1 using 2 with r
  simp [pow_succ, div_eq_mul_inv, mul_comm]

/-- The weights `2⁻⁽ʳ⁺¹⁾` from index `n` on sum to `2⁻ⁿ`. -/
theorem tsum_half_pow_add_succ (n : ℕ) :
    ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + n + 1) = (1 / 2) ^ n := by
  have h (r : ℕ) : (1 / 2 : ℝ) ^ (r + n + 1) = (1 / 2) ^ n * (1 / 2) ^ (r + 1) := by ring
  simp only [h, hasSum_half_pow_succ.summable.tsum_mul_left, hasSum_half_pow_succ.tsum_eq,
    mul_one]

end TauCeti
