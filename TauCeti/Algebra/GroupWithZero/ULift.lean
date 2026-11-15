/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.ULift

/-!
# Zero-divisor and cancellation instances for `ULift`

Mathlib's `Mathlib.Algebra.GroupWithZero.ULift` lifts `MulZeroOneClass`, `MonoidWithZero`, and
`GroupWithZero` structures to `ULift α`, leaving out the `Prop`-valued zero-divisor and
multiplicative cancellation classes from `Mathlib.Algebra.GroupWithZero.InjSurj`. This file
supplies `NoZeroDivisors`, `IsLeftCancelMulZero`, `IsRightCancelMulZero`, and `IsCancelMulZero`
for `ULift α` via `Equiv.ulift.injective`.
-/

public section

assert_not_exists Ring

universe u v

namespace ULift

variable {α : Type u} [Mul α] [Zero α]

instance noZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (ULift.{v} α) :=
  Equiv.ulift.injective.noZeroDivisors _ rfl fun _ _ ↦ rfl

instance isLeftCancelMulZero [IsLeftCancelMulZero α] : IsLeftCancelMulZero (ULift.{v} α) :=
  Equiv.ulift.injective.isLeftCancelMulZero _ rfl fun _ _ ↦ rfl

instance isRightCancelMulZero [IsRightCancelMulZero α] : IsRightCancelMulZero (ULift.{v} α) :=
  Equiv.ulift.injective.isRightCancelMulZero _ rfl fun _ _ ↦ rfl

instance isCancelMulZero [IsCancelMulZero α] : IsCancelMulZero (ULift.{v} α) :=
  Equiv.ulift.injective.isCancelMulZero _ rfl fun _ _ ↦ rfl

end ULift
