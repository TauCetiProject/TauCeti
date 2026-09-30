/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal

/-!
# Internal Hom and restriction of sheaves of modules

Restriction of sheaves of modules to a slice site is strong monoidal. It therefore has a
canonical comparison from the restriction of an internal Hom to the internal Hom of the
restrictions. The comparison is natural in both arguments, and its defining equation says
that evaluation after restriction agrees with the restriction of evaluation.
The named comparison packages the slice site's monoidal and closed instances, which must
otherwise be supplied locally when applying the generic comparison.

The comparison is an isomorphism for every sheaf of modules `M`
(`SheafOfModules.isIso_overIhomComparison`), with no finiteness condition on `M`: restriction
commutes with internal Hom. The internal Hom of sheaves of modules is obtained from that of
presheaves of modules by Day reflection, so forgetting the sheaf condition carries the comparison
for sheaves to the comparison for restriction of presheaves
(`TauCeti.PresheafOfModules.isIso_ihomComparison_pushforward₀_overForget`), up to the
invertible comparisons of the forgetful functors. This uses that restriction commutes with
forgetting the sheaf condition as a lax monoidal functor
(`SheafOfModules.overFunctor_comp_forget_μ`). `SheafOfModules.overIhomIso` and
`SheafOfModules.overDualIso` package the resulting restriction formulas for internal Hom and for
the dual.
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

/-- The monoidal structure on presheaves of modules on the slice site. -/
local instance : MonoidalCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := (R.over X).obj)

/-- The symmetric structure on presheaves of modules on the slice site. -/
local instance : SymmetricCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := (R.over X).obj)

/-- Sheafification on the slice site is monoidal. -/
local instance : (PresheafOfModules.sheafification
    (𝟙 ((ringCatSheaf R).over X).obj)).Monoidal :=
  sheafificationMonoidal (R.over X)

/-- The closed monoidal structure on presheaves of modules on the slice site. -/
local instance : MonoidalClosed
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  presheafMonoidalClosed (R.over X)

/-- The forgetful functor from sheaves of modules to presheaves of modules, as the right adjoint
of sheafification. -/
local notation "sourceForget" =>
  _root_.SheafOfModules.forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The forgetful functor on the slice site, as the right adjoint of sheafification. -/
local notation "targetForget" =>
  _root_.SheafOfModules.forget (Sheaf.over (ringCatSheaf R) X) ⋙
    PresheafOfModules.restrictScalars
      (𝟙 (ObjectProperty.FullSubcategory.obj (Sheaf.over (ringCatSheaf R) X)))

/-- Restriction of presheaves of modules to the slice site. -/
local notation "presheafRestriction" =>
  PresheafOfModules.pushforward (F := Over.forget X)
    (Iso.inv (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) (ringCatSheaf R)))

/-- Restriction of presheaves to the slice is strong monoidal. -/
local instance : (presheafRestriction).Monoidal := by
  -- `pushforwardRingIso` is definitionally `Iso.refl`, so this is the canonical strong monoidal
  -- structure on `pushforward₀OfCommRingCat`, as in `SheafOfModules.overFunctorMonoidal`.
  change (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal
  infer_instance

/-- The sheafification adjunction on the site. -/
local notation "sourceAdjunction" =>
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The sheafification adjunction on the slice site. -/
local notation "targetAdjunction" =>
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (ObjectProperty.FullSubcategory.obj (Sheaf.over (ringCatSheaf R) X)))

/-- Forgetting the sheaf condition turns the internal-Hom comparison for restriction of sheaves
into that for restriction of presheaves: both are the comparison of the composite of restriction
and the forgetful functor. -/
private theorem map_overIhomComparison_app_comp_ihomComparison_app
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := (sourceAdjunction).rightAdjointLaxMonoidal
    letI := (targetAdjunction).rightAdjointLaxMonoidal
    (targetForget).map ((M.overIhomComparison R X).natTrans.app N) ≫
        ((targetForget).ihomComparison (M.over X)).natTrans.app (N.over X) =
      (presheafRestriction).map (((sourceForget).ihomComparison M).natTrans.app N) ≫
        ((presheafRestriction).ihomComparison ((sourceForget).obj M)).natTrans.app
          ((sourceForget).obj N) := by
  let := (sourceAdjunction).rightAdjointLaxMonoidal
  let := (targetAdjunction).rightAdjointLaxMonoidal
  rw [_root_.SheafOfModules.overIhomComparison, ← Functor.ihomComparison_comp,
    ← Functor.ihomComparison_comp, Functor.ihomComparison_app_eq_curry,
    Functor.ihomComparison_app_eq_curry, _root_.SheafOfModules.overFunctor_comp_forget_μ]
  -- The two composite functors agree definitionally, so their images of evaluation agree.
  rfl

/-- After forgetting the sheaf condition, the internal-Hom comparison for restriction is
invertible. -/
private theorem isIso_map_overIhomComparison_app
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso ((targetForget).map ((M.overIhomComparison R X).natTrans.app N)) := by
  let := (sourceAdjunction).rightAdjointLaxMonoidal
  let := (targetAdjunction).rightAdjointLaxMonoidal
  -- The forgetful functors are the reflective right adjoints of Day reflection.
  have : IsIso ((targetForget).ihomComparison (M.over X)).natTrans :=
    Monoidal.Reflective.isIso_ihomComparison (targetAdjunction) (M.over X)
  have : IsIso ((sourceForget).ihomComparison M).natTrans :=
    Monoidal.Reflective.isIso_ihomComparison (sourceAdjunction) M
  have : IsIso ((presheafRestriction).ihomComparison ((sourceForget).obj M)).natTrans :=
    TauCeti.PresheafOfModules.isIso_ihomComparison_pushforward₀_overForget (R := R.obj) X _
  have : IsIso ((targetForget).map ((M.overIhomComparison R X).natTrans.app N) ≫
      ((targetForget).ihomComparison (M.over X)).natTrans.app (N.over X)) := by
    rw [map_overIhomComparison_app_comp_ihomComparison_app]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (NatIso.isIso_app_of_isIso _ _)
  exact IsIso.of_isIso_comp_right _
    (((targetForget).ihomComparison (M.over X)).natTrans.app (N.over X))

/-- Restriction to a slice commutes with internal Hom: the canonical comparison
`𝓗om(M, N)|_X ⟶ 𝓗om(M|_X, N|_X)` is an isomorphism for every sheaf of modules `M`. -/
instance _root_.SheafOfModules.isIso_overIhomComparison
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso (M.overIhomComparison R X).natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have := isIso_map_overIhomComparison_app R X M N
  exact isIso_of_fully_faithful (targetForget) _

/-- The restriction formula for internal Hom out of `M`. -/
def _root_.SheafOfModules.overIhomIso (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    ihom M ⋙ _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ≅
      _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙ ihom (M.over X) :=
  asIso (M.overIhomComparison R X).natTrans

/-- The forward map of the internal-Hom restriction isomorphism is the canonical internal-Hom
comparison. -/
@[simp]
theorem _root_.SheafOfModules.overIhomIso_hom_app
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overIhomIso R X).hom.app N = (M.overIhomComparison R X).natTrans.app N := by
  simp only [_root_.SheafOfModules.overIhomIso, asIso_hom]

/-- The restriction formula for the internal-Hom dual of `M`. The target is the internal Hom into
the tensor unit on the slice site. -/
def _root_.SheafOfModules.overDualIso (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    ((ihom M).obj (_root_.SheafOfModules.unit (ringCatSheaf R))).over X ≅
      (ihom (M.over X)).obj (_root_.SheafOfModules.unit ((ringCatSheaf R).over X)) :=
  (M.overIhomIso R X).app (_root_.SheafOfModules.unit (ringCatSheaf R)) ≪≫
    (ihom (M.over X)).mapIso (_root_.SheafOfModules.overUnitIso (R := R) X)

/-- The forward dual restriction map is the internal-Hom comparison followed by the image of the
monoidal unit comparison. -/
@[simp]
theorem _root_.SheafOfModules.overDualIso_hom (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
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
