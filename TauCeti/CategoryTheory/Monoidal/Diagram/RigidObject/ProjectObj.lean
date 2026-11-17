/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Diagram.RigidObject.Basic

/-!
# Interpreting rigid object expressions in a rigid monoidal category

Given an assignment `f : α → D` of generating objects to objects of a rigid monoidal category `D`,
`TauCeti.RigidObject.projectObj f` evaluates every formal rigid object expression `RigidObject α`
in `D`, sending `.of a` to `f a`, `.unit` to `𝟙_ D`, `.tensor` to tensor product, `.rightDual` to
the chosen right dual, and `.leftDual` to the chosen left dual.

When restricted along `CategoryTheory.FreeMonoidalCategory.toRigidObject`, this agrees with
Mathlib's `CategoryTheory.FreeMonoidalCategory.projectObj`
(`TauCeti.RigidObject.projectObj_toRigidObject`).

## Main definitions and results

* `TauCeti.RigidObject.projectObj`: interpret formal rigid object expressions in an arbitrary
  rigid monoidal category.
* `TauCeti.RigidObject.projectObj_toRigidObject`: compatibility with Mathlib's
  `CategoryTheory.FreeMonoidalCategory.projectObj` on dual-free words.
-/

public section

universe u u' v'

open CategoryTheory MonoidalCategory

namespace TauCeti.RigidObject

variable {α : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RigidCategory D]

/-- Interpret a formal rigid object expression in a rigid monoidal category `D`, sending `.of a` to
`f a`, `.unit` to `𝟙_ D`, `.tensor` to tensor product, `.rightDual` to the chosen right dual, and
`.leftDual` to the chosen left dual. Exposed so dependent morphism types over interpreted boundaries
reduce on constructors, matching `FreeMonoidalCategory.projectObj`. -/
@[expose] noncomputable def projectObj (f : α → D) : RigidObject α → D
  | .of a => f a
  | .unit => 𝟙_ D
  | .tensor X Y => projectObj f X ⊗ projectObj f Y
  | .rightDual X => (projectObj f X)ᘁ
  | .leftDual X => ᘁ(projectObj f X)

@[simp] theorem projectObj_of (f : α → D) (a : α) : projectObj f (.of a) = f a := rfl

@[simp] theorem projectObj_unit (f : α → D) : projectObj f .unit = 𝟙_ D := rfl

@[simp] theorem projectObj_tensor (f : α → D) (X Y : RigidObject α) :
    projectObj f (X.tensor Y) = projectObj f X ⊗ projectObj f Y := rfl

@[simp] theorem projectObj_rightDual (f : α → D) (X : RigidObject α) :
    projectObj f X.rightDual = (projectObj f X)ᘁ := rfl

@[simp] theorem projectObj_leftDual (f : α → D) (X : RigidObject α) :
    projectObj f X.leftDual = ᘁ(projectObj f X) := rfl

/-- Interpreting a dual-free monoidal word after embedding into `RigidObject` agrees with Mathlib's
`FreeMonoidalCategory.projectObj`. -/
@[simp]
theorem projectObj_toRigidObject (f : α → D) (W : FreeMonoidalCategory α) :
    projectObj f W.toRigidObject = FreeMonoidalCategory.projectObj f W := by
  induction W <;> simp_all [FreeMonoidalCategory.projectObj]

end TauCeti.RigidObject
