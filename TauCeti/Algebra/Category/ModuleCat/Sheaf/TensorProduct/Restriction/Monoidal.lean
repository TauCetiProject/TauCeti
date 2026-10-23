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
* `SheafOfModules.overUnitIso`: the resulting unit comparison;
* `SheafOfModules.overFunctor_comp_forget_μ`: restriction commutes with forgetting the sheaf
  condition as a lax monoidal functor, where the forgetful functors carry the lax monoidal
  structures of right adjoints of sheafification.
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
  PresheafOfModulesOfCommRing.monoidalCategory (R := (R.over X).obj)

/-- The symmetric structure on presheaves of modules on the slice site. -/
local instance : SymmetricCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := (R.over X).obj)

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

/-- The sheafification adjunction on the site. -/
local notation "sourceAdjunction" =>
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (ObjectProperty.FullSubcategory.obj (ringCatSheaf R)))

/-- The sheafification adjunction on the slice site. -/
local notation "targetAdjunction" =>
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (ObjectProperty.FullSubcategory.obj (Sheaf.over (ringCatSheaf R) X)))

/-- Restriction of sheaves of modules, as the pushforward along `Over.forget X` in terms of which
the sheafification--restriction comparison is stated. -/
local notation "sheafRestriction" =>
  _root_.SheafOfModules.pushforward (J := J.over X) (K := J) (F := Over.forget X) (𝟙 _)

/-- The inverse tensor comparison, expanded through restriction of presheaves and sheafification
and presented through the counits of the sheafification adjunction. -/
private theorem overTensorIso_inv_eq_counit (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).inv =
        (((sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) ((sourceForget).obj M)).hom) ⊗ₘ
          ((sheafRestriction).map (inv ((sourceAdjunction).counit.app N)) ≫
            (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
              (ringCatSheaf R) ((sourceForget).obj N)).hom)) ≫
        Functor.LaxMonoidal.μ restrictionSheafification ((sourceForget).obj M)
          ((sourceForget).obj N) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
        (sheafRestriction).map
          (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
              ((sourceForget).obj N) ≫
            ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) := by
  rw [_root_.SheafOfModules.overTensorIso_inv]
  -- As in `SheafOfModules.overTensorIso_inv_eq`, unfold the generated monoidal structure to the
  -- localization tensorator before applying its expansion lemma.
  change
    ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
      sourceSheafification sourceW
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      restrictionSheafification).hom.app M).app N = _
  rw [CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
    sourceSheafification sourceW
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
    restrictionSheafification (Y₁ := M) (Y₂ := N)
    (asIso ((sourceAdjunction).counit.app M)).symm
    (asIso ((sourceAdjunction).counit.app N)).symm]
  rw [overSheafificationLifting_iso_hom_app R X, overSheafificationLifting_iso_hom_app R X,
    overSheafificationLifting_iso_inv_app R X]
  rfl

/-- On the sheafification of the restriction of the underlying presheaf of `M`, the counit at the
restriction of `M`, the inverse of the restricted counit at `M`, and the sheafification--restriction
comparison compose to the identity. -/
private theorem counit_comp_map_inv_counit_comp_hom
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (targetAdjunction).counit.app ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M) ≫
        (sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M)).hom = 𝟙 _ := by
  calc _ = ((pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M)).inv ≫
          (sheafRestriction).map ((sourceAdjunction).counit.app M)) ≫
        (sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M)).hom := by
        rw [pushforwardSheafificationIso_inv_comp_map_counit]
        -- The two counits differ only by the unfolding of `SheafOfModules.overFunctor`.
        rfl
    _ = 𝟙 _ := by
        rw [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- The counits at the restrictions of `M` and `N`, followed by the first factor of the expanded
inverse tensor comparison, cancel. -/
private theorem counit_tensorHom_comp_map_inv_counit_tensorHom_comp
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    ((targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M) ⊗ₘ
      (targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)) ≫
      (((sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj M)).hom) ⊗ₘ
        ((sheafRestriction).map (inv ((sourceAdjunction).counit.app N)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj N)).hom)) ≫
      Functor.LaxMonoidal.μ restrictionSheafification ((sourceForget).obj M)
        ((sourceForget).obj N) ≫
      (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
        (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
      (sheafRestriction).map
        (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
            ((sourceForget).obj N) ≫
          ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) =
    Functor.LaxMonoidal.μ restrictionSheafification ((sourceForget).obj M)
        ((sourceForget).obj N) ≫
      (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
        (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
      (sheafRestriction).map
        (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
            ((sourceForget).obj N) ≫
          ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) := by
  have hcancel : ((targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M) ⊗ₘ
      (targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)) ≫
      (((sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj M)).hom) ⊗ₘ
        ((sheafRestriction).map (inv ((sourceAdjunction).counit.app N)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj N)).hom)) = 𝟙 _ := by
    refine (tensorHom_comp_tensorHom _ _ _ _).trans ?_
    rw [counit_comp_map_inv_counit_comp_hom X M,
      counit_comp_map_inv_counit_comp_hom X N]
    exact id_tensorHom_id _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcancel).trans (Category.id_comp _))

/-- The comparison of the tensorators through the counits of the sheafification adjunctions. -/
private theorem δ_comp_counit_tensorHom_comp_map_inv_counit_tensorHom_comp
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.OplaxMonoidal.δ targetSheafification
        ((targetForget).obj ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M))
        ((targetForget).obj ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)) ≫
      ((targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M) ⊗ₘ
      (targetAdjunction).counit.app
        ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)) ≫
      (((sheafRestriction).map (inv ((sourceAdjunction).counit.app M)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj M)).hom) ⊗ₘ
        ((sheafRestriction).map (inv ((sourceAdjunction).counit.app N)) ≫
          (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
            (ringCatSheaf R) ((sourceForget).obj N)).hom)) ≫
      Functor.LaxMonoidal.μ restrictionSheafification ((sourceForget).obj M)
        ((sourceForget).obj N) ≫
      (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
        (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
      (sheafRestriction).map
        (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
            ((sourceForget).obj N) ≫
          ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) =
      (targetSheafification).map (Functor.LaxMonoidal.μ presheafRestriction
          ((sourceForget).obj M) ((sourceForget).obj N)) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
        (sheafRestriction).map
          (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
              ((sourceForget).obj N) ≫
            ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) := by
  rw [counit_tensorHom_comp_map_inv_counit_tensorHom_comp X M N, Functor.LaxMonoidal.comp_μ]
  exact (congrArg (Functor.OplaxMonoidal.δ targetSheafification _ _ ≫ ·)
    (Category.assoc _ _ _)).trans (Functor.Monoidal.δ_μ_assoc targetSheafification _ _ _)

/-- The adjoint of the tensorator of restriction followed by forgetting the sheaf condition. -/
private theorem sheafification_map_μ_overFunctor_comp_forget_comp_counit
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    letI := (targetAdjunction).rightAdjointLaxMonoidal
    (targetSheafification).map
        (Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙
          targetForget) M N) ≫
        (targetAdjunction).counit.app ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj
          (M ⊗ N)) =
      (targetSheafification).map (Functor.LaxMonoidal.μ presheafRestriction
          ((sourceForget).obj M) ((sourceForget).obj N)) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
        (sheafRestriction).map
          (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
              ((sourceForget).obj N) ≫
            ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) := by
  let := (targetAdjunction).rightAdjointLaxMonoidal
  rw [Functor.LaxMonoidal.comp_μ, Functor.map_comp]
  refine (Category.assoc _ _ _).trans ((congrArg ((targetSheafification).map
    (Functor.LaxMonoidal.μ targetForget
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M)
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)) ≫ ·)
    ((targetAdjunction).counit_naturality
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N))).trans
    ?_)
  rw [← Category.assoc, Adjunction.map_μ_comp_counit_app_tensor (adj := targetAdjunction),
    Category.assoc, ← SheafOfModules.overTensorIso_inv, overTensorIso_inv_eq_counit]
  exact δ_comp_counit_tensorHom_comp_map_inv_counit_tensorHom_comp X M N

/-- The adjoint of the tensorator of forgetting the sheaf condition followed by restriction. -/
private theorem sheafification_map_μ_forget_comp_pushforward_comp_counit
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    letI := (sourceAdjunction).rightAdjointLaxMonoidal
    (targetSheafification).map
        (Functor.LaxMonoidal.μ ((sourceForget) ⋙ presheafRestriction) M N) ≫
        (targetAdjunction).counit.app ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj
          (M ⊗ N)) =
      (targetSheafification).map (Functor.LaxMonoidal.μ presheafRestriction
          ((sourceForget).obj M) ((sourceForget).obj N)) ≫
        (pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X)
          (ringCatSheaf R) ((sourceForget).obj M ⊗ (sourceForget).obj N)).inv ≫
        (sheafRestriction).map
          (Functor.OplaxMonoidal.δ sourceSheafification ((sourceForget).obj M)
              ((sourceForget).obj N) ≫
            ((sourceAdjunction).counit.app M ⊗ₘ (sourceAdjunction).counit.app N)) := by
  let := (sourceAdjunction).rightAdjointLaxMonoidal
  rw [Functor.LaxMonoidal.comp_μ, Functor.map_comp]
  refine (Category.assoc _ _ _).trans ((congrArg
    ((targetSheafification).map (Functor.LaxMonoidal.μ presheafRestriction
        ((sourceForget).obj M) ((sourceForget).obj N)) ≫ ·)
    (sheafification_map_pushforward_map_comp_counit (J := J.over X) (K := J)
      (Over.forget X) (ringCatSheaf R) (Functor.LaxMonoidal.μ sourceForget M N))).trans ?_)
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Equiv.symm_apply_apply]

/-- The lax monoidal structure maps of restriction followed by forgetting the sheaf condition
agree with those of forgetting the sheaf condition followed by restriction of presheaves. The
forgetful functors carry the lax monoidal structures of right adjoints of the monoidal
sheafification functors. -/
theorem _root_.SheafOfModules.overFunctor_comp_forget_μ
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    letI := (sourceAdjunction).rightAdjointLaxMonoidal
    letI := (targetAdjunction).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙ targetForget)
        M N =
      Functor.LaxMonoidal.μ ((sourceForget) ⋙ presheafRestriction) M N := by
  -- Both sides are maps into the underlying presheaf of a sheaf, so they are determined by their
  -- adjoint maps out of the sheafification.
  let := (sourceAdjunction).rightAdjointLaxMonoidal
  let := (targetAdjunction).rightAdjointLaxMonoidal
  have key {A : PresheafOfModules.{u} (Sheaf.over (ringCatSheaf R) X).obj}
      {B : SheafOfModules.{u} (ringCatSheaf R)}
      (f : A ⟶ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙ targetForget).obj B)
      (g : A ⟶ ((sourceForget) ⋙ presheafRestriction).obj B)
      (h : (targetSheafification).map f ≫ (targetAdjunction).counit.app
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj B) =
        (targetSheafification).map g ≫ (targetAdjunction).counit.app
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj B)) : f = g :=
    -- The inverse hom-equivalence of an adjunction is `homEquiv_counit` by definition.
    ((targetAdjunction).homEquiv A _).symm.injective h
  exact key _ _ ((sheafification_map_μ_overFunctor_comp_forget_comp_counit X M N).trans
    (sheafification_map_μ_forget_comp_pushforward_comp_counit X M N).symm)

end SheafOfModules

end

end TauCeti
