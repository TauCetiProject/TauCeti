/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Presheaves of modules on a spectrum with scalars restricted to the base ring

Restricting section scalars along `R ≅ Γ(Spec R, ⊤)` turns a presheaf of modules on
`Spec R` into a presheaf of `R`-modules. This is the presheaf counterpart of
`AlgebraicGeometry.modulesSpecToSheaf`, used in affine comparisons before sheafification.
The maps from a module to the sections of its associated sheaf form a natural transformation
from the constant presheaf.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}}

/-- Restrict the scalars of a presheaf of modules on `Spec R` to `R`, retaining its section
carriers and restriction maps. The abbreviation exposes these carriers so that sectionwise
constructions use the original module instances. -/
abbrev specPresheafFunctor :
    PresheafOfModules.{u} (Spec R).ringCatSheaf.obj ⥤
      ((Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R) :=
  PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom)

/-- The maps from a module to the sections of its associated sheaf, natural in the open. -/
def tildeToOpenNatTrans (M : ModuleCat.{u} R) :
    (Functor.const (Spec R).Opensᵒᵖ).obj M ⟶ (modulesSpecToSheaf.obj (tilde M)).obj where
  app U := tilde.toOpen M U.unop
  naturality _ _ i :=
    (Category.id_comp _).trans (tilde.toOpen_res M _ _ i.unop).symm

/-- Each component of the natural transformation to sections is the associated-section map. -/
@[simp]
theorem tildeToOpenNatTrans_app (M : ModuleCat.{u} R) (U : (Spec R).Opensᵒᵖ) :
    (tildeToOpenNatTrans M).app U = tilde.toOpen M U.unop := by
  rfl

end TauCeti.AlgebraicGeometry
