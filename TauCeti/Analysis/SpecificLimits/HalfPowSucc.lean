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
# Partial and infinite sums of the weights `2⁻⁽ʳ⁺¹⁾`

The weights `(1 / 2) ^ (r + 1)` sum to `1` over `r : ℕ` and have partial sums at most `1`, the
normalisation needed to distribute a total tolerance over a sequence of stages or form a bounded
Fréchet series metric.

## Main results

* `TauCeti.hasSum_half_pow_succ`: `HasSum (fun r : ℕ ↦ (1 / 2 : ℝ) ^ (r + 1)) 1`.
* `TauCeti.summable_half_pow_succ`: `Summable (fun r : ℕ ↦ (1 / 2 : ℝ) ^ (r + 1))`.
* `TauCeti.tsum_half_pow_succ`: `(∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1)) = 1`.
* `TauCeti.sum_half_pow_succ_le_one`: the partial sums are at most `1`.
-/

public section

namespace TauCeti

/-- The geometric weights `(1 / 2) ^ (r + 1)` have infinite sum `1`. -/
theorem hasSum_half_pow_succ : HasSum (fun r : ℕ ↦ (1 / 2 : ℝ) ^ (r + 1)) 1 := by
  have h := (hasSum_geometric_two.mul_left (1 / 2 : ℝ))
  simpa only [pow_succ', show (1 / 2 : ℝ) * 2 = 1 by norm_num] using h

/-- The geometric weights `(1 / 2) ^ (r + 1)` are summable. -/
theorem summable_half_pow_succ : Summable (fun r : ℕ ↦ (1 / 2 : ℝ) ^ (r + 1)) :=
  hasSum_half_pow_succ.summable

/-- The infinite series `∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1)` equals `1`. -/
theorem tsum_half_pow_succ : (∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1)) = 1 :=
  hasSum_half_pow_succ.tsum_eq

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
