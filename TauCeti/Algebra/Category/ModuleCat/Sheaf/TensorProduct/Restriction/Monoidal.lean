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

The construction descends the evident symmetric monoidal structure on restriction of presheaves
through sheafification.  The localization universal property supplies all monoidal coherence laws;
the proof that the descended structure preserves the braiding uses the same localization comparison.

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

/-- Sheafification on the source site of restriction to a slice. -/
abbrev overSourceSheafification :=
  PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)

/-- Sheafification on the slice site. -/
abbrev overTargetSheafification :=
  PresheafOfModules.sheafification.{u} (𝟙 ((ringCatSheaf R).over X).obj)

/-- Restriction of presheaves of modules to a slice. -/
abbrev overPresheafFunctor :=
  PresheafOfModules.pushforward (F := Over.forget X)
    (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) (ringCatSheaf R)).inv

/-- Restriction of presheaves followed by sheafification on the slice. -/
abbrev overSheafification :=
  overPresheafFunctor R X ⋙ overTargetSheafification R X

/-- The local isomorphisms inverted by sheafification on the source site. -/
abbrev overSourceW : MorphismProperty
    (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf.{u} (ringCatSheaf R).obj)

/-- The natural comparison exhibits restriction as a lift of presheaf restriction followed by
sheafification. -/
@[instance_reducible]
def overSheafificationLifting : CategoryTheory.Localization.Lifting
    (overSourceSheafification R) (overSourceW R)
    (overSheafification R X) (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) where
  iso := overSheafificationNatIso (ringCatSheaf R) X

local instance : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

local instance : SymmetricCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  symmetricCategory (R.over X)

local instance : MonoidalCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModules.monoidalCategory (R := (R.over X).obj)

local instance : SymmetricCategory
    (PresheafOfModules.{u} ((ringCatSheaf R).over X).obj) :=
  PresheafOfModules.symmetricCategory (R := (R.over X).obj)

/-- The monoidal structure on restriction of presheaves used in the descent construction. -/
@[instance_reducible]
def overPresheafFunctorMonoidal : (overPresheafFunctor R X).Monoidal :=
  inferInstanceAs
    ((PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal)

/-- Restriction of presheaves preserves the sectionwise symmetric braiding. -/
@[instance_reducible]
def overPresheafFunctorBraided : (overPresheafFunctor R X).Braided := by
  letI : (overPresheafFunctor R X).Monoidal := overPresheafFunctorMonoidal R X
  exact { braided _ _ := by rfl }

/-- Sheafification on the slice is a braided monoidal functor. -/
@[instance_reducible]
def overTargetSheafificationBraided : (overTargetSheafification R X).Braided :=
  sheafificationBraided (R.over X)

/-- Restriction of presheaves followed by sheafification is braided monoidal. -/
@[instance_reducible]
def overSheafificationBraided : (overSheafification R X).Braided := by
  letI : (overPresheafFunctor R X).Braided := overPresheafFunctorBraided R X
  letI : (overTargetSheafification R X).Braided := overTargetSheafificationBraided R X
  exact @Functor.Braided.instComp _ _ _ _ _ _ _ _ _ _ _ _
    (overPresheafFunctor R X) (overTargetSheafification R X) inferInstance inferInstance

/-- Restriction of sheaves of modules to a slice is a strong monoidal functor. -/
instance overFunctorMonoidal :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Monoidal :=
  @CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    _ _ _ _ _ _ _ _ _
    (overSourceSheafification R) (overSourceW R) _ _
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) (overSheafification R X)
    (overSheafificationBraided R X).toMonoidal _ (overSheafificationLifting R X)

/-- Restriction of sheaves of modules to a slice preserves the symmetric braiding. -/
instance overFunctorBraided :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).Braided where
  braided M N := by
    let _ : CategoryTheory.Localization.Lifting
        (overSourceSheafification R) (overSourceW R)
        (overSheafification R X)
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
      overSheafificationLifting R X
    let _ : (overSheafification R X).Braided := overSheafificationBraided R X
    let _ : (overSheafification R X).Monoidal :=
      (overSheafificationBraided R X).toMonoidal
    change
      ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
        (overSourceSheafification R) (overSourceW R)
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
        (overSheafification R X)).hom.app M).app N ≫
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map (β_ M N).hom =
        (β_ ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj M)
          ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj N)).hom ≫
          ((CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost
            (overSourceSheafification R) (overSourceW R)
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
            (overSheafification R X)).hom.app N).app M
    rw [CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      (overSourceSheafification R) (overSourceW R)
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      (overSheafification R X) (sheafificationIso (ringCatSheaf R) M).symm
      (sheafificationIso (ringCatSheaf R) N).symm,
      CategoryTheory.Localization.Monoidal.curriedTensorPreIsoPost_hom_app_app'
      (overSourceSheafification R) (overSourceW R)
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)
      (overSheafification R X) (sheafificationIso (ringCatSheaf R) N).symm
      (sheafificationIso (ringCatSheaf R) M).symm]
    simp only [Category.assoc, ← Functor.map_comp]
    -- Move the source braiding across the inverse tensorator of sheafification.
    have sheafification_braiding :
        Functor.OplaxMonoidal.δ (overSourceSheafification R) M.val N.val ≫
            (β_ ((overSourceSheafification R).obj M.val)
              ((overSourceSheafification R).obj N.val)).hom =
          (overSourceSheafification R).map (β_ M.val N.val).hom ≫
            Functor.OplaxMonoidal.δ (overSourceSheafification R) N.val M.val := by
      rw [← cancel_mono (Functor.LaxMonoidal.μ
        (overSourceSheafification R) N.val M.val)]
      simp
    rw [BraidedCategory.braiding_naturality, reassoc_of% sheafification_braiding,
      Functor.map_comp]
    -- Naturality moves the mapped source braiding through the localization comparison.
    have lifting_naturality :
        (overSheafification R X).map (β_ M.val N.val).hom ≫
            (CategoryTheory.Localization.Lifting.iso
              (overSourceSheafification R) (overSourceW R) (overSheafification R X)
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (N.val ⊗ M.val) =
          (CategoryTheory.Localization.Lifting.iso
              (overSourceSheafification R) (overSourceW R) (overSheafification R X)
              (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.app
                (M.val ⊗ N.val) ≫
            (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
              ((overSourceSheafification R).map (β_ M.val N.val).hom) :=
      (CategoryTheory.Localization.Lifting.iso
        (overSourceSheafification R) (overSourceW R) (overSheafification R X)
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).inv.naturality
          (β_ M.val N.val).hom
    rw [← reassoc_of% lifting_naturality]
    -- The presheaf restriction--sheafification composite already preserves braidings.
    have presheaf_braiding :
        Functor.LaxMonoidal.μ (overSheafification R X) M.val N.val ≫
            (overTargetSheafification R X).map
              ((overPresheafFunctor R X).map (β_ M.val N.val).hom) =
          (β_ ((overSheafification R X).obj M.val)
            ((overSheafification R X).obj N.val)).hom ≫
            Functor.LaxMonoidal.μ (overSheafification R X) N.val M.val :=
      Functor.LaxBraided.braided (F := overSheafification R X) M.val N.val
    rw [reassoc_of% presheaf_braiding]
    -- Finish by naturality of the target braiding with respect to the comparison maps.
    have comparison_braiding := BraidedCategory.braiding_naturality
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) M).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          (overSourceSheafification R) (overSourceW R) (overSheafification R X)
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app M.val)
      ((_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).map
          (sheafificationIso (ringCatSheaf R) N).symm.hom ≫
        (CategoryTheory.Localization.Lifting.iso
          (overSourceSheafification R) (overSourceW R) (overSheafification R X)
          (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).hom.app N.val)
    rw [reassoc_of% comparison_braiding]

variable {R}

/-- The tensor comparison for restriction to a slice. -/
@[expose]
def _root_.SheafOfModules.overTensorIso
    (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : C) :
    @Iso (SheafOfModules.{u} (ringCatSheaf (R.over X))) _ ((M ⊗ N).over X)
      (M.over X ⊗ N.over X) :=
  (Functor.Monoidal.μIso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N).symm

/-- The unit comparison for restriction to a slice. -/
@[expose]
def _root_.SheafOfModules.overUnitIso (X : C) :
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).obj
        (𝟙_ (SheafOfModules.{u} (ringCatSheaf R))) ≅
      𝟙_ (SheafOfModules.{u} (ringCatSheaf (R.over X))) :=
  (Functor.Monoidal.εIso
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X)).symm

@[simp]
theorem overTensorIso_hom (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).hom =
      Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N :=
  rfl

@[simp]
theorem overTensorIso_inv (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (M.overTensorIso N X).inv =
      Functor.LaxMonoidal.μ
        (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N :=
  rfl

@[simp]
theorem overUnitIso_hom : (_root_.SheafOfModules.overUnitIso (R := R) X).hom =
    Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
  rfl

@[simp]
theorem overUnitIso_inv : (_root_.SheafOfModules.overUnitIso (R := R) X).inv =
    Functor.LaxMonoidal.ε
      (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) :=
  rfl

end SheafOfModules

end

end TauCeti
