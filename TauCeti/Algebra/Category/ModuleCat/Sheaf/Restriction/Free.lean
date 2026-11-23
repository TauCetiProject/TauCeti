/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction.Unit

/-!
# Open-subspace restriction of free sheaves of modules

Using the open-subspace restriction `TopologicalSpace.Opens.sheafOfModulesRestrict` and its
preservation of the unit sheaf (`TopologicalSpace.Opens.sheafOfModulesRestrictUnitIso`),
restriction to an open subspace `U` preserves free module sheaves
(`TopologicalSpace.Opens.sheafOfModulesRestrictFreeIso`). Under Mathlib's slice equivalence
`U.sheafOfModulesEquivOver R`, free module sheaves on the slice site over `U` also correspond to
free module sheaves on the open subspace `U`
(`TopologicalSpace.Opens.sheafOfModulesEquivOverFunctorObjFreeIso`).

## Main declarations

* `TopologicalSpace.Opens.sheafOfModulesEquivOverFunctorObjFreeIso` (with generator formula
  `sheafOfModulesEquivOver_functor_map_ιFree_comp_sheafOfModulesEquivOverFunctorObjFreeIso_hom`):
  free module sheaves and basis generators under `sheafOfModulesEquivOver`;
* `TopologicalSpace.Opens.sheafOfModulesRestrictFreeIso` (with generator formula
  `sheafOfModulesRestrict_map_ιFree_comp_sheafOfModulesRestrictFreeIso_hom`):
  free module sheaves and basis generators under `sheafOfModulesRestrict`.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

namespace TopologicalSpace.Opens

section FreeRestriction

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

/-- Under `U.sheafOfModulesEquivOver R`, free module sheaves on the slice site over `U` correspond
to free module sheaves on the open subspace `U`. -/
def sheafOfModulesEquivOverFunctorObjFreeIso (I : Type u) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  let F : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (U.sheafRestrict.obj R) :=
    (U.sheafOfModulesEquivOver R).functor
  haveI : PreservesColimitsOfShape (Discrete I) F :=
    (U.sheafOfModulesEquivOver R).toAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso F I (U.sheafOfModulesEquivOverUnit R).symm).symm

/-- Through `sheafOfModulesEquivOverFunctorObjFreeIso`, the image of a free generator `ιFree i`
is `ιFree i` on the open subspace `U` precomposed with the unit comparison. -/
@[reassoc (attr := simp)]
theorem sheafOfModulesEquivOver_functor_map_ιFree_comp_sheafOfModulesEquivOverFunctorObjFreeIso_hom
    (I : Type u) (i : I) :
    (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.ιFree i) ≫
        (U.sheafOfModulesEquivOverFunctorObjFreeIso R I).hom =
      (U.sheafOfModulesEquivOverUnit R).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.map_ιFree_mapFreeIso_inv _ I _ i

/-- Open-subspace restriction sends the free module sheaf on `I` to the free module sheaf on `I`. -/
def sheafOfModulesRestrictFreeIso (I : Type u) :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  haveI : PreservesColimitsOfShape (Discrete I) (U.sheafOfModulesRestrict.{u} R) :=
    (U.sheafOfModulesRestrictAdj.{u} R).leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso (U.sheafOfModulesRestrict.{u} R) I
    (U.sheafOfModulesRestrictUnitIso R).symm).symm

/-- Through `sheafOfModulesRestrictFreeIso`, restricting a free generator `ιFree i` gives
`ιFree i` on the open subspace `U` precomposed with `sheafOfModulesRestrictUnitIso`. -/
@[reassoc (attr := simp)]
theorem sheafOfModulesRestrict_map_ιFree_comp_sheafOfModulesRestrictFreeIso_hom
    (I : Type u) (i : I) :
    (U.sheafOfModulesRestrict.{u} R).map (SheafOfModules.ιFree i) ≫
        (U.sheafOfModulesRestrictFreeIso R I).hom =
      (U.sheafOfModulesRestrictUnitIso R).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.map_ιFree_mapFreeIso_inv _ I _ i

end FreeRestriction

end TopologicalSpace.Opens

end
