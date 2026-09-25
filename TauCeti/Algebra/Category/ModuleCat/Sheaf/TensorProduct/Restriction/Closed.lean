/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Internal Hom and restriction of sheaves of modules

Restriction of sheaves of modules to a slice site is strong monoidal. It therefore has a
canonical comparison from the restriction of an internal Hom to the internal Hom of the
restrictions. The comparison is natural in both arguments, and its defining equation says
that evaluation after restriction agrees with the restriction of evaluation.
The named comparison packages the slice site's monoidal and closed instances, which must
otherwise be supplied locally when applying the generic comparison.  In particular,
`SheafOfModules.overIhomComparison_free` proves that restriction preserves the comparison
for the free rank-one sheaf.

This is the comparison map needed to study local duality and internal Homs on a cover.
It is not asserted to be an isomorphism for arbitrary sheaves of modules.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u}) (X : C)

/-- The monoidal structure on sheaves of modules on the slice site. -/
local instance : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The closed monoidal structure on sheaves of modules on the slice site. -/
local instance : MonoidalClosed
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalClosed (R.over X)

/-- The canonical internal Hom comparison for restriction to the slice over `X`.
Its component at `N` maps the restriction of `𝓗om(M,N)` to
`𝓗om(M|_X,N|_X)`. -/
def _root_.SheafOfModules.overIhomComparison
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    TwoSquare (ihom M) (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      (ihom (M.over X)) :=
  CategoryTheory.Functor.ihomComparison
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M

-- A pre-lemma (`simp↓`, as in #8642): otherwise `Functor.comp_obj`, `Functor.id_obj` and
-- `SheafOfModules.ihom_obj` rewrite the implicit source and target objects of the comparison's
-- component first, and the left-hand side no longer matches.
/-- Evaluation characterizes the internal Hom comparison for restriction: after the monoidal
tensorator it agrees with restricting the evaluation map. -/
@[reassoc (attr := simp↓)]
theorem _root_.SheafOfModules.overIhomComparison_ev
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (M.over X) ◁ (M.overIhomComparison R X).natTrans.app N ≫
        (ihom.ev (M.over X)).app (N.over X) =
      Functor.LaxMonoidal.μ
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
          M ((ihom M).obj N) ≫
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          ((ihom.ev M).app N) :=
  CategoryTheory.Functor.ihomComparison_ev
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N

/-- Restriction preserves the internal-Hom comparison for the free rank-one sheaf. -/
theorem _root_.SheafOfModules.overIhomComparison_free :
    IsIso ((_root_.SheafOfModules.overIhomComparison R X
      (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit)).natTrans) := by
  apply CategoryTheory.Functor.ihomComparison_isIso_of_iso_unit
    (F := _root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    (A := _root_.SheafOfModules.free (R := ringCatSheaf R) PUnit)
  · exact CategoryTheory.Functor.ihomComparison_unit _
  · exact freePUnitIsoUnit (ringCatSheaf R)

end SheafOfModules

end

end TauCeti
