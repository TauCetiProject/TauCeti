/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Transporting internal actions by lax monoidal functors

A lax monoidal functor carries an action of a monoid object to an action of the image
monoid object. The action map is the tensorator followed by the image of the original
action. Equivariant morphisms remain equivariant. This applies, in particular, to passing
from algebra coactions to actions on affine schemes by a monoidal spectrum functor.

The construction follows Mathlib's `CategoryTheory.Functor.monObjObj`, using the same
tensorator and coherence identities.
-/

public section

open CategoryTheory MonoidalCategory MonObj
open Functor.LaxMonoidal

namespace CategoryTheory.Functor

open scoped Obj

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
  (M X : C) [MonObj M] [ModObj M X]

/-- A lax monoidal functor transports an internal action to an action of the image monoid. -/
@[instance_reducible]
def modObjObj : ModObj (F.obj M) (F.obj X) where
  smul := LaxMonoidal.μ F M X ≫ F.map γ[M, X]
  one_smul := by simp [← F.map_comp]
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight, obj.μ_def]
    simp only [comp_whiskerRight, Category.assoc, μ_natural_left_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul_self]
    simp

/-- The transported action is the tensorator followed by the image of the action. -/
@[simp]
theorem modObjObj_smul :
    letI := F.modObjObj M X
    γ[F.obj M, F.obj X] = LaxMonoidal.μ F M X ≫ F.map γ[M, X] := by
  rw [modObjObj]
  rfl

variable {X} {Y : C} [ModObj M Y]

/-- A lax monoidal functor transports equivariant morphisms to equivariant morphisms. -/
theorem modObjObj_isModHom (f : X ⟶ Y) [IsModHom M f] :
    letI := F.modObjObj M X
    letI := F.modObjObj M Y
    IsModHom (F.obj M) (F.map f) := by
  let := F.modObjObj M X
  let := F.modObjObj M Y
  constructor
  simp only [modObjObj_smul, selfLeftAction_actionHomRight, Category.assoc,
    μ_natural_right_assoc, ← F.map_comp]
  exact congrArg (fun k ↦ LaxMonoidal.μ F M X ≫ F.map k) (IsModHom.smul_hom (A := M) (f := f))

end CategoryTheory.Functor
