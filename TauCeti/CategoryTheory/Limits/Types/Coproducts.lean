/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Coproducts in the category of types

This file records the colimit cofan presenting a type `M : Type u` as the coproduct of `M` copies
of `PUnit.{u + 1}` (`TauCeti.Types.isColimitPUnitCofan`).
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Types

/-- A type `M : Type u` is the categorical coproduct of `M` copies of `PUnit.{u + 1}` via the
singleton-picking inclusions `m ↦ (fun _ ↦ m)`. -/
noncomputable def isColimitPUnitCofan (M : Type u) :
    IsColimit (Cofan.mk M (fun m ↦ TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ m))) :=
  Cofan.IsColimit.mk _ (fun s ↦ TypeCat.ofHom fun m ↦ s.inj m PUnit.unit)
    (fun s m ↦ by ext ⟨⟩; rfl)
    (fun s f hf ↦ by ext m; exact congrArg (fun g ↦ g PUnit.unit) (hf m))

/-- The universal map out of `isColimitPUnitCofan M` sends `m : M` to `s.inj m PUnit.unit`. -/
@[simp]
theorem isColimitPUnitCofan_desc (M : Type u)
    (s : Cofan (fun _ : M ↦ PUnit.{u + 1})) :
    (isColimitPUnitCofan M).desc s = TypeCat.ofHom fun m ↦ s.inj m PUnit.unit :=
  (rfl)

/-- The universal map out of `isColimitPUnitCofan M` evaluates at `m : M` by applying the `m`-th
injection of the target cofan to `PUnit.unit`. -/
theorem isColimitPUnitCofan_desc_apply (M : Type u)
    (s : Cofan (fun _ : M ↦ PUnit.{u + 1})) (m : M) :
    (isColimitPUnitCofan M).desc s m = s.inj m PUnit.unit :=
  (rfl)

end TauCeti.Types
