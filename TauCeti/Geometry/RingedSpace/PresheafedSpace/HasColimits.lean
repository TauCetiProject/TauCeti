/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.SheafedSpace

/-!
# Colimits of presheafed spaces with sheaf structure presheaves

The structure presheaf of a colimit `X` of a diagram `F` of presheafed spaces is the limit of the
pushforwards to `X` of the structure presheaves of the `F j`
(`AlgebraicGeometry.PresheafedSpace.colimitCocone`). Pushforwards and limits of sheaves are
sheaves, so if every `F j` has a sheaf structure presheaf, so does every colimit of `F`. This is
the statement behind Mathlib's instance that the forgetful functor from sheafed spaces to
presheafed spaces creates colimits, phrased for an arbitrary colimit cocone of presheafed spaces,
so that it applies to colimits constructed in other categories and transported to presheafed
spaces, such as glued spaces.

## Main results

* `AlgebraicGeometry.PresheafedSpace.isSheaf_of_isColimit`: the structure presheaf of a colimit of
  presheafed spaces whose structure presheaves are sheaves is a sheaf.
-/

public section

open CategoryTheory Limits Opposite TopCat

namespace AlgebraicGeometry.PresheafedSpace

universe w w' v u

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] [Small.{v} J]
  [HasLimitsOfShape Jᵒᵖ C]

/-- **A colimit of sheafed spaces, computed among presheafed spaces, is a sheafed space.** If every
object of a diagram `F` of presheafed spaces has a sheaf structure presheaf, then so does the cocone
point of every colimit cocone of `F`: the structure presheaf of the colimit is a limit of
pushforwards of sheaves. -/
theorem isSheaf_of_isColimit (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (hF : ∀ j, (F.obj j).presheaf.IsSheaf) {c : Cocone F} (hc : IsColimit c) :
    c.pt.presheaf.IsSheaf :=
  let e := hc.coconePointUniqueUpToIso (colimitCoconeIsColimit F)
  Presheaf.isSheaf_of_iso (asIso e.inv.c).symm (Sheaf.pushforward_sheaf_of_sheaf _
    (limit_isSheaf _ fun j ↦ Sheaf.pushforward_sheaf_of_sheaf _ (hF (unop j))))

end AlgebraicGeometry.PresheafedSpace
