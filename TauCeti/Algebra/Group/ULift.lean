/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ULift

/-!
# The isomorphism between a magma and its universe lift

The multiplicative isomorphism `MulEquiv.ulift : ULift α ≃* α` is `ULift.down`, with inverse
`ULift.up`. This file records both as simplification rules.

## Main results

* `MulEquiv.ulift_apply`: `MulEquiv.ulift x = x.down`.
* `MulEquiv.ulift_symm_apply`: `MulEquiv.ulift.symm x = ULift.up x`.
-/

public section

universe u v

namespace MulEquiv

variable {α : Type u} [Mul α]

/-- The isomorphism `MulEquiv.ulift : ULift α ≃* α` evaluates by `ULift.down`. -/
@[to_additive (attr := simp) /-- The isomorphism `AddEquiv.ulift : ULift α ≃+ α` evaluates by
`ULift.down`. -/]
theorem ulift_apply (x : ULift.{v} α) : MulEquiv.ulift x = x.down :=
  (rfl)

/-- The inverse of the isomorphism `MulEquiv.ulift : ULift α ≃* α` evaluates by `ULift.up`. -/
@[to_additive (attr := simp) /-- The inverse of the isomorphism `AddEquiv.ulift : ULift α ≃+ α`
evaluates by `ULift.up`. -/]
theorem ulift_symm_apply (x : α) : (MulEquiv.ulift : ULift.{v} α ≃* α).symm x = ULift.up x :=
  (rfl)

end MulEquiv
