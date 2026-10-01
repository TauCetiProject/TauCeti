/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quadratic Taylor estimate for the exponential of a Banach algebra

The exponential of a complete normed algebra agrees with its quadratic truncation
`1 + x + 2⁻¹ • x ^ 2` to third order at the origin.  This file records that estimate in
`Asymptotics.IsBigO` form.

The exponential is analytic at `0` with power series `NormedSpace.expSeries`, so the statement is
the Taylor formula `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` at `n = 3`, once the third partial
sum of `expSeries` is evaluated.  The first-order statement, that `exp x = 1 + x` to second order,
is the derivative of the exponential at the origin and is already available through
`NormedSpace.hasFDerivAt_exp_zero`; what is new here is the next order, which is what the
second-order term of the Baker--Campbell--Hausdorff expansion consumes.

## Main results

* `NormedSpace.expSeries_partialSum_three`: the third partial sum of the exponential series is
  `1 + x + 2⁻¹ • x ^ 2`.
* `NormedSpace.isBigO_exp_sub_quadratic`: `exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` at the
  origin.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff", whose first-order law is proved from this
  estimate in `TauCeti/Analysis/Normed/Algebra/BCH/FirstOrder.lean`.
-/

public section

open Asymptotics Filter Topology
open scoped Nat

noncomputable section

namespace NormedSpace

variable (𝕂 : Type*) {A : Type*} [NontriviallyNormedField 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A]

/-- The third partial sum of the exponential series is the quadratic truncation
`1 + x + 2⁻¹ • x ^ 2`. -/
theorem expSeries_partialSum_three (x : A) :
    (expSeries 𝕂 A).partialSum 3 x = 1 + x + (2⁻¹ : 𝕂) • x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, expSeries_apply_eq,
    Nat.factorial]

variable [CharZero 𝕂] [ContinuousSMul ℚ 𝕂] [CompleteSpace A]

/-- **The quadratic Taylor estimate for the exponential.**  In a complete normed algebra,
`exp x - (1 + x + 2⁻¹ • x ^ 2)` is `O(‖x‖ ^ 3)` as `x → 0`. -/
theorem isBigO_exp_sub_quadratic :
    (fun x : A ↦ exp x - (1 + x + (2⁻¹ : 𝕂) • x ^ 2)) =O[𝓝 (0 : A)] fun x ↦ ‖x‖ ^ 3 := by
  simpa only [zero_add, expSeries_partialSum_three] using
    (exp_hasFPowerSeriesAt_zero (𝕂 := 𝕂) (𝔸 := A)).isBigO_sub_partialSum_pow 3

end NormedSpace
