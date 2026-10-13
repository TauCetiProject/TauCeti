/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# The sign of the Rayleigh form on the kernel and range of the positive part

Let `B` be a bounded self-adjoint operator on a Hilbert space over `ℝ` or `ℂ`, and let `B⁺` be
its positive part, defined by the continuous functional calculus. The kernel and the range of
`B⁺` separate the vectors according to the sign of the Rayleigh form `re ⟪B x, x⟫`:

* on the kernel of `B⁺`, `re ⟪B x, x⟫ ≤ 0`, because `B ≤ B⁺`;
* on the range of `B⁺`, `0 ≤ re ⟪B x, x⟫`, because `B B⁺ = B⁺ B⁺` and `B⁺` is positive.

Since `B⁺` is self-adjoint, its kernel is the orthogonal complement of its range. Applied to
`B = A - s`, the two statements play the role of the spectral projections of `A` onto `(-∞, s]`
and `(s, ∞)` while using only the continuous functional calculus.

The continuous functional calculus `ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint` is
taken as a hypothesis, as in Mathlib's `ContinuousLinearMap.instStarOrderedRingRCLike`; Mathlib
provides it for complex Hilbert spaces.

## Main declarations

* `ContinuousLinearMap.re_inner_nonpos_of_posPart_apply_eq_zero`: on the kernel of `B⁺`, the
  Rayleigh form of `B` is nonpositive.
* `ContinuousLinearMap.re_inner_nonneg_of_mem_range_posPart`: on the range of `B⁺`, the Rayleigh
  form of `B` is nonnegative.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- On the kernel of the positive part `B⁺` of a self-adjoint operator `B`, the Rayleigh form of
`B` is nonpositive. -/
theorem re_inner_nonpos_of_posPart_apply_eq_zero {B : E →L[𝕜] E} (hB : IsSelfAdjoint B) {x : E}
    (hx : B⁺ x = 0) : re ⟪B x, x⟫_𝕜 ≤ 0 := by
  have := instStarOrderedRingRCLike (𝕜 := 𝕜) (H := E)
  have h := (le_def.mp (CFC.le_posPart hB)).re_inner_nonneg_left x
  rwa [sub_apply, hx, zero_sub, inner_neg_left, map_neg, neg_nonneg] at h

/-- On the range of the positive part `B⁺` of an operator `B`, the Rayleigh form of `B` is
nonnegative. -/
theorem re_inner_nonneg_of_mem_range_posPart {B : E →L[𝕜] E} {x : E} (hx : x ∈ B⁺.range) :
    0 ≤ re ⟪B x, x⟫_𝕜 := by
  have := instStarOrderedRingRCLike (𝕜 := 𝕜) (H := E)
  obtain ⟨y, rfl⟩ := hx
  rw [coe_coe]
  by_cases hB : IsSelfAdjoint B
  · -- `B B⁺ = (B⁺ - B⁻) B⁺ = B⁺ B⁺`, since `B⁻ B⁺ = 0`.
    have hmul : B * B⁺ = B⁺ * B⁺ := by
      nth_rw 1 [← CFC.posPart_sub_negPart B]
      rw [sub_mul, CFC.negPart_mul_posPart, sub_zero]
    have h := (nonneg_iff_isPositive.mp (CFC.posPart_nonneg B)).re_inner_nonneg_left (B⁺ y)
    rwa [← mul_apply_eq_comp, ← hmul, mul_apply_eq_comp] at h
  · simp [CFC.posPart_eq_zero_of_not_isSelfAdjoint hB]

end ContinuousLinearMap

end
