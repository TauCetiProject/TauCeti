/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-!
# Restriction as a symmetric monoidal functor

For a sheaf of commutative rings `R` on a small site and an object `X` of the site, this file
equips restriction to the slice over `X` with a strong symmetric monoidal structure.

The coherent tensor and unit comparisons allow tensor units, evaluation, and coevaluation maps to
be transported through restriction to slice sites. They are the local compatibility needed when
studying dualizable and finite locally free sheaves on a cover.

The descent construction uses Mathlib's
[`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Localization/Monoidal/Functor.html#CategoryTheory.Localization.Monoidal.functorMonoidalOfComp).

## Main declarations

* `SheafOfModules.overFunctorMonoidal`: restriction to a slice is strong monoidal;
* `SheafOfModules.overFunctorBraided`: restriction preserves the symmetric braiding;
* `SheafOfModules.overTensorIso`: the resulting tensor comparison;
* `SheafOfModules.overUnitIso`: the resulting unit comparison.
-/

public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u}) (X : C)

/-- The source sheafification functor used to descend restriction to sheaves. -/
local notation "sourceSheafification" =>
  PresheafOfModules.sheafification
    (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The sheafification functor on the slice site used to descend restriction. -/
local notation "targetSheafification" =>
  PresheafOfModules.sheafification
    (𝟙 (ObjectProperty.FullSubcategory.obj (Sheaf.over (ringCatSheaf R) X)))

/-- Restriction of presheaves of modules to the slice site. -/
local notation "presheafRestriction" =>
  PresheafOfModules.pushforward (F := Over.forget X)
    (Iso.inv (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X)
      (ringCatSheaf R)))

/-- Restriction of presheaves followed by sheafification on the slice site. -/
local notation "restrictionSheafification" => presheafRestriction ⋙ targetSheafification

/-- The source morphisms inverted by sheafification. -/
local notation "sourceW" =>
  MorphismProperty.inverseImage (J.W (A := AddCommGrpCat))
    (PresheafOfModules.toPresheaf (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The localization lifting comparing restriction after source sheafification with restriction
followed by target sheafification. -/
local instance overSheafificationLifting : CategoryTheory.Localization.Lifting
    sourceSheafification sourceW restrictionSheafification
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) where
  iso := overSheafificationNatIso (ringCatSheaf R) X

private theorem overSheafificationLifting_iso_hom_app
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    (CategoryTheory.Localization.Lifting.iso sourceSheafification sourceW
      restrictionSheafification
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app P =
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) P).hom := by
  -- The localization lifting stores `overSheafificationNatIso` in its `iso` field. Rewriting its
  -- component lemma cannot expose that field projection, so reduce the projection first.
  change (overSheafificationNatIso (ringCatSheaf R) X).hom.app P = _
  exact overSheafificationNatIso_hom_app (ringCatSheaf R) X P

private theorem overSheafificationLifting_iso_inv_app
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    (CategoryTheory.Localization.Lifting.iso sourceSheafification sourceW
      restrictionSheafification
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app P =
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) P).inv := by
  -- As above, expose the natural isomorphism stored in the localization lifting before applying
  -- its public component characterization.
  change (overSheafificationNatIso (ringCatSheaf R) X).inv.app P = _
  exact overSheafificationNatIso_inv_app (ringCatSheaf R) X P

/-- The monoidal structure on sheaves of modules on the slice site. -/
local instance : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The symmetric structure on sheaves of modules on the slice site. -/
local instance : SymmetricCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  symmetricCategory (R.over X)

/-- The monoidal structure on presheaves of modules on the slice site. -/
local instance : MonoidalCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModules.monoidalCategory (R := (R.over X).obj)

/-- The symmetric structure on presheaves of modules on the slice site. -/
local instance : SymmetricCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModules.symmetricCategory (R := (R.over X).obj)

/-- Restriction of presheaves to the slice is strong monoidal. -/
local instance overPresheafFunctorMonoidal : (presheafRestriction).Monoidal := by
  -- `pushforwardRingIso` is definitionally `Iso.refl`, so this is the canonical strong monoidal
  -- structure on `pushforward₀OfCommRingCat`, not a separately chosen tensorator.
  change (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal
  infer_instance

/-- Restriction of presheaves to the slice preserves the braiding. -/
local instance overPresheafFunctorBraided : (presheafRestriction).Braided where
  -- After the preceding identification, both the canonical pushforward tensorator and the
  -- braiding are defined sectionwise, so their compatibility is pointwise reflexivity.
  braided _ _ := by
    rfl

/-- Sheafification on the slice site preserves the braiding. -/
local instance overTargetSheafificationBraided : (targetSheafification).Braided :=
  sheafificationBraided (R.over X)

/-- Restriction of presheaves followed by slice sheafification preserves the braiding. -/
local instance overSheafificationBraided : (restrictionSheafification).Braided := by
  exact @Functor.Braided.instComp _ _ _ _ _ _ _ _ _ _ _ _
    presheafRestriction targetSheafification inferInstance inferInstance

private theorem overCurriedTensorPreIsoPost_hom_app_app
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification).hom.app M).app N =
        (((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              (sheafificationIso (ringCatSheaf R) M).symm.hom ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) M.val).hom) ⊗ₘ
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              (sheafificationIso (ringCatSheaf R) N).symm.hom ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) N.val).hom)) ≫
        Functor.LaxMonoidal.μ restrictionSheafification M.val N.val ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) (M.val ⊗ N.val)).inv ≫
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (Functor.OplaxMonoidal.δ sourceSheafification M.val N.val ≫
            ((sheafificationIso (ringCatSheaf R) M).symm.inv ⊗ₘ
              (sheafificationIso (ringCatSheaf R) N).symm.inv)) := by
  rw [CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
    sourceSheafification sourceW
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    restrictionSheafification (sheafificationIso (ringCatSheaf R) M).symm
    (sheafificationIso (ringCatSheaf R) N).symm]
  rw [overSheafificationLifting_iso_hom_app R X M.val,
    overSheafificationLifting_iso_hom_app R X N.val,
    overSheafificationLifting_iso_inv_app R X (M.val ⊗ N.val)]
  rfl

/-- Restriction of sheaves of modules to a slice is a strong monoidal functor. -/
instance _root_.SheafOfModules.overFunctorMonoidal :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Monoidal :=
  @CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _ sourceSheafification sourceW _ _
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) restrictionSheafification
    (overSheafificationBraided R X).toMonoidal _ (overSheafificationLifting R X)

/-- Restriction of sheaves of modules to a slice preserves the symmetric braiding. -/
instance _root_.SheafOfModules.overFunctorBraided :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Braided where
  braided M N := by
    let _ : CategoryTheory.Localization.Lifting
        sourceSheafification sourceW
        restrictionSheafification
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
      overSheafificationLifting R X
    let _ : (restrictionSheafification).Braided := overSheafificationBraided R X
    let _ : (restrictionSheafification).Monoidal :=
      (overSheafificationBraided R X).toMonoidal
    -- `Functor.Braided` asks for the tensorator on arbitrary sheaves, whereas the localization
    -- comparison lemmas describe it after choosing sheafification presentations. This `change`
    -- is the definitional bridge from the generated `functorMonoidalOfComp` tensorator to the
    -- public `curriedTensorPreIsoPost` characterization used below.
    change
      ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
        sourceSheafification sourceW
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
        restrictionSheafification).hom.app M).app N ≫
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map (β_ M N).hom =
        (β_ ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M)
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)).hom ≫
          ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
            sourceSheafification sourceW
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
            restrictionSheafification).hom.app N).app M
    rw [CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification (sheafificationIso (ringCatSheaf R) M).symm
      (sheafificationIso (ringCatSheaf R) N).symm,
      CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification (sheafificationIso (ringCatSheaf R) N).symm
      (sheafificationIso (ringCatSheaf R) M).symm]
    simp only [Category.assoc, ← Functor.map_comp]
    -- Move the source braiding across the inverse tensorator of sheafification.
    have sheafification_braiding :
        Functor.OplaxMonoidal.δ sourceSheafification M.val N.val ≫
            (β_ ((sourceSheafification).obj M.val)
              ((sourceSheafification).obj N.val)).hom =
          (sourceSheafification).map (β_ M.val N.val).hom ≫
            Functor.OplaxMonoidal.δ sourceSheafification N.val M.val := by
      rw [← cancel_mono (Functor.LaxMonoidal.μ
        sourceSheafification N.val M.val)]
      simp
    rw [BraidedCategory.braiding_naturality, reassoc_of% sheafification_braiding,
      Functor.map_comp]
    -- Naturality moves the mapped source braiding through the localization comparison.
    have lifting_naturality :
        (restrictionSheafification).map (β_ M.val N.val).hom ≫
            (CategoryTheory.Localization.Lifting.iso
              sourceSheafification sourceW restrictionSheafification
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (N.val ⊗ M.val) =
          (CategoryTheory.Localization.Lifting.iso
              sourceSheafification sourceW restrictionSheafification
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (M.val ⊗ N.val) ≫
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              ((sourceSheafification).map (β_ M.val N.val).hom) :=
      (CategoryTheory.Localization.Lifting.iso
        sourceSheafification sourceW restrictionSheafification
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.naturality
          (β_ M.val N.val).hom
    rw [← reassoc_of% lifting_naturality]
    -- The presheaf restriction--sheafification composite already preserves braidings.
    have presheaf_braiding :
        Functor.LaxMonoidal.μ restrictionSheafification M.val N.val ≫
            (targetSheafification).map
              ((presheafRestriction).map (β_ M.val N.val).hom) =
          (β_ ((restrictionSheafification).obj M.val)
            ((restrictionSheafification).obj N.val)).hom ≫
            Functor.LaxMonoidal.μ restrictionSheafification N.val M.val :=
      Functor.LaxBraided.braided (F := restrictionSheafification) M.val N.val
    rw [reassoc_of% presheaf_braiding]
    -- Finish by naturality of the target braiding with respect to the comparison maps.
    have comparison_braiding := BraidedCategory.braiding_naturality
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) M).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          sourceSheafification sourceW restrictionSheafification
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app M.val)
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) N).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          sourceSheafification sourceW restrictionSheafification
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app N.val)
    rw [reassoc_of% comparison_braiding]

variable {R}

/-- The tensor comparison for restriction to a slice. -/
def _root_.SheafOfModules.overTensorIso
    (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : C) :
    @Iso (SheafOfModules.{u} (ringCatSheaf (R.over X))) _ ((M ⊗ N).over X)
      (M.over X ⊗ N.over X) :=
  (Functor.Monoidal.μIso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N).symm

/-- The unit comparison for restriction to a slice. -/
def _root_.SheafOfModules.overUnitIso (X : C) :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj
        (𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅
      𝟙_ (SheafOfModules.{u} (ringCatSheaf (R.over X))) :=
  (Functor.Monoidal.εIso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).symm

/-- The forward tensor comparison is the oplax monoidal structure map of restriction. -/
@[simp]
theorem _root_.SheafOfModules.overTensorIso_hom
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).hom =
      Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N :=
  (rfl)

/-- The inverse tensor comparison is the lax monoidal structure map of restriction. -/
@[simp]
theorem _root_.SheafOfModules.overTensorIso_inv
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).inv =
      Functor.LaxMonoidal.μ
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N :=
  (rfl)

/-- The inverse tensor comparison, expanded through restriction of presheaves and
sheafification. -/
theorem _root_.SheafOfModules.overTensorIso_inv_eq
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).inv =
        (((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              (sheafificationIso (ringCatSheaf R) M).symm.hom ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) M.val).hom) ⊗ₘ
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              (sheafificationIso (ringCatSheaf R) N).symm.hom ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) N.val).hom)) ≫
        Functor.LaxMonoidal.μ
          (PresheafOfModules.pushforward (F := Over.forget X)
              (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X)
                (ringCatSheaf R)).inv ⋙
            PresheafOfModules.sheafification
              (𝟙 ((ringCatSheaf R).over X).obj)) M.val N.val ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) (M.val ⊗ N.val)).inv ≫
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (Functor.OplaxMonoidal.δ
              (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) M.val N.val ≫
            ((sheafificationIso (ringCatSheaf R) M).symm.inv ⊗ₘ
              (sheafificationIso (ringCatSheaf R) N).symm.inv)) := by
  rw [_root_.SheafOfModules.overTensorIso_inv]
  -- `overTensorIso` is defined from the generated monoidal structure. Its inverse reduces to the
  -- localization tensorator only definitionally, before the public expansion lemma can apply.
  change
    ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification).hom.app M).app N = _
  exact overCurriedTensorPreIsoPost_hom_app_app R X M N

/-- The forward unit comparison is the oplax monoidal unit map of restriction. -/
@[simp]
theorem _root_.SheafOfModules.overUnitIso_hom :
    (_root_.SheafOfModules.overUnitIso (R := R) X).hom =
    Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
  (rfl)

/-- The inverse unit comparison is the lax monoidal unit map of restriction. -/
@[simp]
theorem _root_.SheafOfModules.overUnitIso_inv :
    (_root_.SheafOfModules.overUnitIso (R := R) X).inv =
    Functor.LaxMonoidal.ε
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
  (rfl)

/-- The inverse unit comparison, expanded through restriction of presheaves and
sheafification. -/
theorem _root_.SheafOfModules.overUnitIso_inv_eq :
    (_root_.SheafOfModules.overUnitIso (R := R) X).inv =
    Functor.LaxMonoidal.ε
        (PresheafOfModules.pushforward (F := Over.forget X)
            (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R)).inv ⋙
          PresheafOfModules.sheafification
            (𝟙 ((ringCatSheaf R).over X).obj)) ≫
      (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
        (ringCatSheaf R) (𝟙_ (PresheafOfModules (ringCatSheaf R).obj))).inv ≫
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
        (Functor.OplaxMonoidal.η
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))) := by
  rw [_root_.SheafOfModules.overUnitIso_inv]
  -- The unit comparison is defined from the generated monoidal structure, so unfold that
  -- definitional wrapper before using `functorMonoidalOfComp_ε`.
  change Functor.LaxMonoidal.ε
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) = _
  rw [CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε
    sourceSheafification sourceW
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    restrictionSheafification]
  rw [overSheafificationLifting_iso_inv_app R X]
  rfl

end SheafOfModules

end

end TauCeti
