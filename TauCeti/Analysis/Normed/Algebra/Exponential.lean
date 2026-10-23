/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quadratic truncation and Taylor estimate for the exponential

For an algebra `A` over a field, with `A` a topological ring, the third partial sum of
`NormedSpace.expSeries` is `1 + x + 2⁻¹ • x ^ 2`. This identity needs no norm or completeness
assumption.
In a complete normed algebra, the exponential agrees with this quadratic truncation to third
order at the origin. This file records that estimate in `Asymptotics.IsBigO` form.

The exponential is analytic at `0` with power series `NormedSpace.expSeries`, so the statement is
the Taylor formula `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` at `n = 3`, once the third partial
sum of `expSeries` is evaluated. The quadratic order pins down the second-order term of the
Baker--Campbell--Hausdorff expansion.

## Main results

* `NormedSpace.expSeries_partialSum_three`: the third partial sum of the exponential series is
  `1 + x + 2⁻¹ • x ^ 2`.
* `NormedSpace.isBigO_exp_sub_quadratic`: `exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` at the
  origin.
-/

public section

open Asymptotics Filter Topology
open scoped Nat

noncomputable section

namespace NormedSpace

section Algebra

variable (𝕂 : Type*) {A : Type*} [Field 𝕂] [Ring A] [Algebra 𝕂 A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- For an algebra `A` over a field, with `A` a topological ring, the third partial sum of the
exponential series is the quadratic truncation `1 + x + 2⁻¹ • x ^ 2`. -/
@[simp]
theorem expSeries_partialSum_three (x : A) :
    (expSeries 𝕂 A).partialSum 3 x = 1 + x + (2⁻¹ : 𝕂) • x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, expSeries_apply_eq,
    Nat.factorial]

end Algebra

variable (𝕂 : Type*) {A : Type*} [NontriviallyNormedField 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]
  [CharZero 𝕂] [ContinuousSMul ℚ 𝕂] [CompleteSpace A]

/-- **The quadratic Taylor estimate for the exponential.**  In a complete normed algebra,
`exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` as `x → 0`. -/
theorem isBigO_exp_sub_quadratic :
    (fun x : A ↦ exp x - (1 + x + (2⁻¹ : 𝕂) • x ^ 2)) =O[𝓝 (0 : A)] fun x ↦ ‖x‖ ^ 3 := by
  simpa only [zero_add, expSeries_partialSum_three] using
    (exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A)).isBigO_sub_partialSum_pow 3

end NormedSpace
