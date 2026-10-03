/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Module structures on restrictions to slice sites

Restricting a sheaf of modules to the slice over an object preserves its section modules.
For a commutative coefficient sheaf, these sections retain the action of the original
commutative ring of sections after forgetting commutativity in the coefficient sheaf.

## Main declarations

* `SheafOfModules.overSectionModule`: the original commutative-ring action on sections of
  a sheaf of modules restricted to a slice site.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Restriction to a slice uses the original commutative-ring action on each section module. -/
instance _root_.SheafOfModules.overSectionModule
    {R : Sheaf J CommRingCat.{u}} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (P : _root_.SheafOfModules.{v} (ringCatSheaf R)) (U V : C) (g : V ⟶ U) :
    Module (R.obj.obj (Opposite.op V)) ((P.over U).val.obj (Opposite.op (Over.mk g))) :=
  inferInstanceAs (Module (R.obj.obj (Opposite.op V)) (P.val.obj (Opposite.op V)))

end SheafOfModules

end

end TauCeti
