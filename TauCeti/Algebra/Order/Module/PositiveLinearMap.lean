/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Faithfulness kernels of positive linear maps

A faithful positive linear map on a proper star-ordered ring vanishes on `star a * a` only when
`a = 0` (`PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`).

## Main declarations

* `PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`: a faithful positive linear map on
  a proper star-ordered ring has trivial quadratic kernel on `star a * a`.
-/

public section

namespace PositiveLinearMap

/-- A faithful positive linear map on a proper star-ordered ring vanishes on `star a * a` only
when `a = 0`. -/
theorem eq_zero_of_faithful_apply_star_mul_self {A 𝕜 E : Type*} [NonUnitalSemiring A]
    [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    [Semiring 𝕜] [AddCommMonoid E] [PartialOrder E] [Module 𝕜 A] [Module 𝕜 E]
    (f : A →ₚ[𝕜] E) (hf : ∀ a : A, 0 ≤ a → a ≠ 0 → 0 < f a) {a : A}
    (ha : f (star a * a) = 0) : a = 0 := by
  by_contra ha0
  exact (hf _ (star_mul_self_nonneg a) (star_mul_self_eq_zero.not.2 ha0)).ne' ha

end PositiveLinearMap
