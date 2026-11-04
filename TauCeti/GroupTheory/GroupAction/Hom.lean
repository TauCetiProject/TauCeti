/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Equivariant maps to the point and constant equivariant maps

Two elementary equivariant maps which `Mathlib/GroupTheory/GroupAction/Hom.lean` leaves
unrecorded: the unique equivariant map to the one-point space `PUnit`, and the constant equivariant
map whose value is a fixed point.

## Main declarations

* `MulActionHom.toPUnit`: the equivariant map from any space to the point.
* `MulActionHom.constOfMemFixedPoints`: the constant equivariant map at a fixed point.
-/

public section

open MulAction

universe w

namespace MulActionHom

variable {M N X Y : Type*} [SMul M X] {φ : M → N}

variable (X φ) in
/-- The equivariant map from `X` to the point. -/
def toPUnit : X →ₑ[φ] PUnit.{w + 1} :=
  ⟨fun _ ↦ PUnit.unit, fun _ _ ↦ rfl⟩

variable (X φ) in
theorem coe_toPUnit : ⇑(toPUnit.{w} X φ) = Function.const X PUnit.unit :=
  (rfl)

variable [Monoid N] [MulAction N Y]

/-- The equivariant map from `X` with constant value a fixed point `y` of `Y`. -/
def constOfMemFixedPoints {y : Y} (hy : y ∈ fixedPoints N Y) : X →ₑ[φ] Y :=
  ⟨fun _ ↦ y, fun m _ ↦ (hy (φ m)).symm⟩

@[simp]
theorem constOfMemFixedPoints_apply {y : Y} (hy : y ∈ fixedPoints N Y) (x : X) :
    constOfMemFixedPoints (φ := φ) hy x = y :=
  (rfl)

theorem coe_constOfMemFixedPoints {y : Y} (hy : y ∈ fixedPoints N Y) :
    ⇑(constOfMemFixedPoints (X := X) (φ := φ) hy) = Function.const X y :=
  (rfl)

end MulActionHom
