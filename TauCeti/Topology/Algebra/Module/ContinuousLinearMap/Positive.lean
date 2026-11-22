/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import TauCeti.Algebra.Order.Module.PositiveLinearMap

/-!
# Faithfulness kernels of positive continuous linear maps

A faithful positive continuous linear map on a proper star-ordered ring vanishes on `star a * a`
only when `a = 0` (`PositiveContinuousLinearMap.eq_zero_of_faithful_apply_star_mul_self`).

## Main declarations

* `PositiveContinuousLinearMap.eq_zero_of_faithful_apply_star_mul_self`: a faithful positive
  continuous linear map on a proper star-ordered ring has trivial quadratic kernel on `star a * a`.
-/

public section

namespace PositiveContinuousLinearMap

/-- A faithful positive continuous linear map on a proper star-ordered ring vanishes on
`star a * a` only when `a = 0`. -/
theorem eq_zero_of_faithful_apply_star_mul_self {A 𝕜 E : Type*} [NonUnitalSemiring A]
    [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    [Semiring 𝕜] [AddCommMonoid E] [PartialOrder E] [TopologicalSpace A] [TopologicalSpace E]
    [Module 𝕜 A] [Module 𝕜 E] (ψ : A →P[𝕜] E)
    (hψ : ∀ a : A, 0 ≤ a → a ≠ 0 → 0 < ψ a) {a : A} (ha : ψ (star a * a) = 0) : a = 0 :=
  ψ.toPositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self hψ ha

end PositiveContinuousLinearMap
