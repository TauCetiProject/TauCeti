/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Colimit
public import Mathlib.Condensed.Discrete.Module

/-!
# Locally constant functions to a module on a cofiltered limit of finite sets

Mathlib shows that the presheaf of sets `S ↦ LocallyConstant S X` on profinite sets turns a
cofiltered limit of finite sets with surjective projections into a colimit
(`Condensed.isColimitLocallyConstantPresheaf`). This file records the same statement for the
presheaf of `R`-modules `S ↦ LocallyConstant S M`
(`Condensed.isColimitLocallyConstantModulePresheaf`), since the forgetful functor from modules to
sets reflects filtered colimits.
-/

public section

universe u

open CategoryTheory Limits Functor

noncomputable section

namespace Condensed

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone (F ⋙ FintypeCat.toProfinite)) {R : Type (u + 1)} [Ring R] (M : ModuleCat.{u + 1} R)

/-- Forgetting the module structure of the cocone of locally constant functions to `M` on the
finite quotients of `c` gives the cocone of locally constant functions to the underlying set of
`M`: both have the same cocone point `LocallyConstant c.pt M`, and both legs pull back along the
projections of `c`. -/
private def forgetMapCoconeIso :
    (CategoryTheory.forget (ModuleCat.{u + 1} R)).mapCocone
        (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj M).mapCocone
          c.op) ≅
      (locallyConstantPresheaf M).mapCocone c.op :=
  Cocone.ext (Iso.refl _)

/-- The presheaf of `R`-modules `S ↦ LocallyConstant S M` on profinite sets takes cofiltered
limits of finite sets with surjective projection maps to colimits. This is the module-valued
version of `Condensed.isColimitLocallyConstantPresheaf`. -/
def isColimitLocallyConstantModulePresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit (((CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R).obj
      M).mapCocone c.op) :=
  let : ReflectsFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    reflectsFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  isColimitOfReflects (CategoryTheory.forget (ModuleCat.{u + 1} R))
    ((isColimitLocallyConstantPresheaf c M hc).ofIsoColimit (forgetMapCoconeIso c M).symm)

end Condensed
