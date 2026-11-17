/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Coercion and idempotence lemmas for `PositiveLinearMap.ofClass`

`PositiveLinearMap.ofClass` reinterprets any map carrying `LinearMapClass` and `OrderHomClass`
instances as a bundled `PositiveLinearMap`. This module supplies the `@[simp]` function-coercion and
self-reinterpretation lemmas (`PositiveLinearMap.coe_ofClass` and `PositiveLinearMap.ofClass_self`)
so declarations returning `PositiveLinearMap.ofClass` simplify without unfolding its definition.
-/

public section

namespace PositiveLinearMap

variable {F R E₁ E₂ : Type*} [Semiring R] [AddCommMonoid E₁] [PartialOrder E₁]
  [AddCommMonoid E₂] [PartialOrder E₂] [Module R E₁] [Module R E₂]

/-- Coercing `PositiveLinearMap.ofClass f` to a function recovers `f`. -/
@[simp]
theorem coe_ofClass [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂] [OrderHomClass F E₁ E₂]
    (f : F) : ⇑(ofClass f) = f := by
  rw [← coe_toLinearMap]
  simp [ofClass]

/-- Reinterpreting a bundled `PositiveLinearMap` via `PositiveLinearMap.ofClass` is the identity. -/
@[simp]
theorem ofClass_self (f : E₁ →ₚ[R] E₂) : ofClass f = f := by
  ext x
  simp

end PositiveLinearMap
