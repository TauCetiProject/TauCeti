/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs

/-!
# Module structures on stalks of sheaves of modules

The stalk of a sheaf of modules over a sheaf of rings is a module over the ring stalk.
For commutative coefficient rings, it also retains the module action
of the original commutative ring stalk when the coefficient sheaf forgets commutativity.
The instances `SheafOfModules.ringCatStalkModule` and `SheafOfModules.stalkModule` expose
Mathlib's presheaf stalk module structures independently of the internal Hom construction.
-/

public section

open CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}}

/-- The stalk of a sheaf of modules over an ordinary ring sheaf carries Mathlib's module
structure over the stalk of that ring sheaf. -/
instance ringCatStalkModule {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (P : SheafOfModules.{u} R) (x : X) :
    Module ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk P.val.presheaf x) :=
  let Q : PresheafOfModules.{u} R.obj := P.val
  inferInstanceAs (Module ↑(TopCat.Presheaf.stalk R.obj x)
    ↑(TopCat.Presheaf.stalk Q.presheaf x))

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The stalk of a sheaf of modules carries Mathlib's module structure over the stalk of
the original commutative-ring sheaf. The carrier and action are unchanged by forgetting
commutativity in the coefficient sheaf. -/
instance stalkModule (P : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)) (x : X) :
    Module ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk P.val.presheaf x) :=
  let Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) := P.val
  inferInstanceAs (Module ↑(TopCat.Presheaf.stalk R.obj x)
    ↑(TopCat.Presheaf.stalk Q.presheaf x))

end SheafOfModules
