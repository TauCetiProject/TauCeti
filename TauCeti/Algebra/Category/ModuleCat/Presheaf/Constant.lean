/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Presheaves of `R`-modules as modules over the constant presheaf of rings

Let `R` be a ring and `C` a category. A presheaf of `R`-modules `F : Cᵒᵖ ⥤ ModuleCat R` is a
presheaf of modules over the constant presheaf of rings with value `R`: its sections and
restriction maps are unchanged, and the restriction maps are linear over the identity of `R`.
This is the form in which Mathlib's constructions for presheaves of modules over a presheaf of
rings, such as `PresheafOfModules.sheafify`, apply to presheaves of `R`-modules.

## Main declarations

* `PresheafOfModules.ofPresheafModuleCat R`: the functor
  `(Cᵒᵖ ⥤ ModuleCat R) ⥤ PresheafOfModules (constant presheaf R)`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type*} [Category* C] (R : Type u) [Ring R]

/-- A presheaf of `R`-modules, regarded as a presheaf of modules over the constant presheaf of
rings with value `R`. Its underlying presheaf of abelian groups is that of the given presheaf. -/
@[simps]
noncomputable def ofPresheafModuleCat :
    (Cᵒᵖ ⥤ ModuleCat.{v} R) ⥤ PresheafOfModules.{v} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj F :=
    letI (U : Cᵒᵖ) : Module ((Functor.const Cᵒᵖ).obj (RingCat.of R) |>.obj U)
        ((F ⋙ forget₂ _ AddCommGrpCat).obj U) :=
      inferInstanceAs (Module R (F.obj U))
    ofPresheaf (F ⋙ forget₂ _ _) (fun _ _ f r m ↦ (F.map f).hom.map_smul r m)
  map g := homMk (Functor.whiskerRight g (forget₂ _ AddCommGrpCat))
    (fun U r m ↦ (g.app U).hom.map_smul r m)

end PresheafOfModules
