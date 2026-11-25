/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Coercion of `PositiveLinearMap.ofClass`

Mathlib's `PositiveLinearMap.ofClass` reinterprets an element of a type of positive linear maps as
a bundled positive linear map, but has no lemma computing its coercion to a function. This file
supplies the simp lemma `PositiveLinearMap.coe_ofClass`, matching `LinearMap.coe_ofClass` and
`PositiveContinuousLinearMap.coe_ofClass`.
-/

public section

namespace PositiveLinearMap

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- The positive linear map `PositiveLinearMap.ofClass f` has the same underlying function as
`f`. -/
@[simp]
theorem coe_ofClass (f : F) : ⇑(ofClass f : E₁ →ₚ[R] E₂) = f :=
  rfl

end PositiveLinearMap
