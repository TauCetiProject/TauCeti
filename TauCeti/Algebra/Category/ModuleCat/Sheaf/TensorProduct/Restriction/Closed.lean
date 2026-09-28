/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Dual
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Internal Hom and restriction of sheaves of modules

Restriction of sheaves of modules to a slice site is strong monoidal. It therefore has a
canonical comparison from the restriction of an internal Hom to the internal Hom of the
restrictions. The comparison is natural in both arguments, and its defining equation says
that evaluation after restriction agrees with the restriction of evaluation.
The named comparison packages the slice site's monoidal and closed instances, which must
otherwise be supplied locally when applying the generic comparison.

The comparison is an isomorphism when its source is a finite free sheaf
(`SheafOfModules.overIhomComparison_free_isIso`): such a sheaf is its own dual, and restriction,
being strong monoidal, carries this self-duality to the slice. The same holds for any sheaf
isomorphic to a finite free one (`SheafOfModules.overIhomComparison_isIso_of_iso_free`). This is
the local input for comparing internal Homs and duals of finite locally free sheaves on a cover.
The comparison is not asserted to be an isomorphism for arbitrary sheaves of modules; wherever it
is invertible, `SheafOfModules.overIhomIso` and `SheafOfModules.overDualIso` package the
resulting restriction formulas for internal Hom and for the dual.
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

/-- Restriction to a slice inverts the internal-Hom comparison out of a finite free sheaf: the
free sheaf on a finite type is its own dual, and restriction is strong monoidal. -/
theorem _root_.SheafOfModules.overIhomComparison_free_isIso (I : Type u) [Finite I] :
    IsIso ((_root_.SheafOfModules.overIhomComparison R X
      (_root_.SheafOfModules.free (R := ringCatSheaf R) I)).natTrans) :=
  CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    (_root_.SheafOfModules.free (R := ringCatSheaf R) I) (_root_.SheafOfModules.free I)

/-- Restriction to a slice inverts the internal-Hom comparison out of any sheaf isomorphic to a
finite free sheaf. -/
theorem _root_.SheafOfModules.overIhomComparison_isIso_of_iso_free
    {M : _root_.SheafOfModules.{u} (ringCatSheaf R)} (I : Type u) [Finite I]
    (e : M ≅ _root_.SheafOfModules.free (R := ringCatSheaf R) I) :
    IsIso (M.overIhomComparison R X).natTrans :=
  CategoryTheory.Functor.ihomComparison_isIso_of_iso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    (_root_.SheafOfModules.overIhomComparison_free_isIso R X I) e

/-- The restriction formula for internal Hom out of `M`, whenever the internal-Hom comparison for
restriction is invertible. -/
def _root_.SheafOfModules.overIhomIso (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    [IsIso (M.overIhomComparison R X).natTrans] :
    ihom M ⋙ _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ≅
      _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙ ihom (M.over X) :=
  asIso (M.overIhomComparison R X).natTrans

/-- The forward map of the internal-Hom restriction isomorphism is the canonical internal-Hom
comparison. -/
@[simp]
theorem _root_.SheafOfModules.overIhomIso_hom_app
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    [IsIso (M.overIhomComparison R X).natTrans] (N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overIhomIso R X).hom.app N = (M.overIhomComparison R X).natTrans.app N := by
  simp only [_root_.SheafOfModules.overIhomIso, asIso_hom]

/-- The restriction formula for the internal-Hom dual of `M`, whenever the internal-Hom
comparison for restriction is invertible. The target is the internal Hom into the tensor unit on
the slice site. -/
def _root_.SheafOfModules.overDualIso (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    [IsIso (M.overIhomComparison R X).natTrans] :
    ((ihom M).obj (_root_.SheafOfModules.unit (ringCatSheaf R))).over X ≅
      (ihom (M.over X)).obj (_root_.SheafOfModules.unit ((ringCatSheaf R).over X)) :=
  (M.overIhomIso R X).app (_root_.SheafOfModules.unit (ringCatSheaf R)) ≪≫
    (ihom (M.over X)).mapIso (_root_.SheafOfModules.overUnitIso (R := R) X)

/-- The forward dual restriction map is the internal-Hom comparison followed by the image of the
monoidal unit comparison. -/
@[simp]
theorem _root_.SheafOfModules.overDualIso_hom (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    [IsIso (M.overIhomComparison R X).natTrans] :
    (M.overDualIso R X).hom =
      (M.overIhomComparison R X).natTrans.app (_root_.SheafOfModules.unit (ringCatSheaf R)) ≫
        (ihom (M.over X)).map (_root_.SheafOfModules.overUnitIso (R := R) X).hom := by
  simp only [_root_.SheafOfModules.overDualIso, Iso.trans_hom, Iso.app_hom,
    _root_.SheafOfModules.overIhomIso_hom_app]
  -- `overUnitIso` is an isomorphism over `ringCatSheaf (R.over X)`, which is only definitionally
  -- `(ringCatSheaf R).over X`, so `simp` cannot rewrite with `Functor.mapIso_hom` here.
  exact congrArg _ (Functor.mapIso_hom _ _)

end SheafOfModules

end

end TauCeti
