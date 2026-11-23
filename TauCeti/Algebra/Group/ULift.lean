/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ULift

/-!
# Evaluation lemmas for `MulEquiv.ulift` and `AddEquiv.ulift`

This file provides `@[simp]` evaluation rules for `MulEquiv.ulift : ULift α ≃* α` and its inverse,
together with their additive counterparts `AddEquiv.ulift_apply` and `AddEquiv.ulift_symm_apply`.

## Main results

* `MulEquiv.ulift_apply`, `AddEquiv.ulift_apply`: `MulEquiv.ulift x = x.down` and
  `AddEquiv.ulift x = x.down`.
* `MulEquiv.ulift_symm_apply`, `AddEquiv.ulift_symm_apply`: `MulEquiv.ulift.symm x = ULift.up x`
  and `AddEquiv.ulift.symm x = ULift.up x`.
-/

public section

universe u v

namespace MulEquiv

variable {α : Type u} [Mul α]

/-- The multiplicative equivalence `ULift α ≃* α` evaluates to `ULift.down`. -/
@[to_additive (attr := simp) /-- The additive equivalence `ULift α ≃+ α` evaluates to
`ULift.down`. -/]
theorem ulift_apply (x : ULift.{v} α) : (ulift : ULift.{v} α ≃* α) x = x.down :=
  (rfl)

/-- The inverse of `MulEquiv.ulift` evaluates to `ULift.up`. -/
@[to_additive (attr := simp) /-- The inverse of `AddEquiv.ulift` evaluates to `ULift.up`. -/]
theorem ulift_symm_apply (x : α) : (ulift : ULift.{v} α ≃* α).symm x = ULift.up.{v} x :=
  (rfl)

end MulEquiv
