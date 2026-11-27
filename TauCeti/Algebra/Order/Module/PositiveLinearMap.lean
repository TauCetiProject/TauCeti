/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Coercion and faithfulness kernels of positive linear maps

Mathlib's `PositiveLinearMap.ofClass` reinterprets an element of a type of positive linear maps as
a bundled positive linear map, and `PositiveLinearMap.mk₀` builds one from a linear map that
preserves nonnegativity, but neither has an application/coercion simp lemma. This file supplies
`PositiveLinearMap.coe_ofClass`, `PositiveLinearMap.mk₀_apply`, and
`PositiveLinearMap.toLinearMap_mk₀`, matching `PositiveContinuousLinearMap`.

A faithful positive linear map on a proper star-ordered ring vanishes on `star a * a` only when
`a = 0` (`PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`).

## Main declarations

* `PositiveLinearMap.coe_ofClass`: coercion of `PositiveLinearMap.ofClass f` as a function.
* `PositiveLinearMap.mk₀_apply`: evaluating `PositiveLinearMap.mk₀ f hf` at `x`.
* `PositiveLinearMap.toLinearMap_mk₀`: linear map underlying `PositiveLinearMap.mk₀ f hf`.
* `PositiveLinearMap.eq_zero_of_faithful_apply_star_mul_self`: a faithful positive linear map on
  a proper star-ordered ring has trivial quadratic kernel on `star a * a`.
-/

public section

namespace PositiveLinearMap

section OfClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- The positive linear map `PositiveLinearMap.ofClass f` has the same underlying function as
`f`. -/
@[simp]
theorem coe_ofClass (f : F) : ⇑(ofClass f : E₁ →ₚ[R] E₂) = f :=
  rfl

end OfClass

section AddGroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂]

/-- Evaluating `PositiveLinearMap.mk₀ f hf` at `x` gives `f x`. -/
@[simp]
theorem mk₀_apply (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) (x : E₁) :
    mk₀ f hf x = f x :=
  rfl

/-- The linear map underlying `PositiveLinearMap.mk₀ f hf` is `f`. -/
@[simp]
theorem toLinearMap_mk₀ (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) :
    (mk₀ f hf).toLinearMap = f :=
  rfl

end AddGroup

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
