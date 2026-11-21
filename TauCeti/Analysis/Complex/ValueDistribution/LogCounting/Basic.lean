/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.LocallyFinsupp

/-!
# Pointwise bounds for logarithmic counting weights

Nevanlinna's logarithmic counting function weights a divisor `D` on a closed ball `closedBall 0 r`
by the radial logarithmic factors `(D z : ℝ) * Real.log (r * ‖z‖⁻¹)`. In
`Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic` (by Stefan Kebekus), nonnegativity of
these summands is proved inline for restrictions `toClosedBall r D` of whole-space divisors under
`1 ≤ r`.

This file provides the standalone pointwise nonnegativity lemma
`Function.locallyFinsuppWithin.mul_log_nonneg_of_subset_closedBall` for any nonnegative
`D : Function.locallyFinsuppWithin U ℤ` supported in `U ⊆ Metric.closedBall 0 r` over a seminormed
additive commutative group, with no `1 ≤ r`, `ProperSpace`, or global-support assumption.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1.1.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.1.
-/

public section

namespace Function.locallyFinsuppWithin

/-- Each radial logarithmic weight `(D z : ℝ) * Real.log (r * ‖z‖⁻¹)` is nonnegative for a
nonnegative `locallyFinsuppWithin` supported inside `Metric.closedBall 0 r` (when `‖z‖ = 0`,
`Real.log 0 = 0`, and outside `U`, `D z = 0`). -/
theorem mul_log_nonneg_of_subset_closedBall {E : Type*} [SeminormedAddCommGroup E]
    {U : Set E} {r : ℝ} {D : locallyFinsuppWithin U ℤ}
    (hU : U ⊆ Metric.closedBall 0 r) (hD : 0 ≤ D) (z : E) :
    0 ≤ (D z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  by_cases hzu : z ∈ U
  · refine mul_nonneg (Int.cast_nonneg (hD z)) (Real.log_nonneg ?_)
    rw [← div_eq_mul_inv, one_le_div ((norm_nonneg z).lt_of_ne' hz0)]
    exact mem_closedBall_zero_iff.1 (hU hzu)
  · simp [apply_eq_zero_of_notMem _ hzu]

end Function.locallyFinsuppWithin
