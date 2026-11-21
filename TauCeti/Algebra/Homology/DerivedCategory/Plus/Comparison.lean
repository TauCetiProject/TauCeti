/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Functor
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.RightDerived
public import TauCeti.Algebra.Homology.Embedding.MapExtend

/-!
# Comparison theorems for bounded-below right derived functors

This file proves two comparison theorems for Mathlib's bounded-below right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`:

* **Exact-functor comparison:** if `F₁ ⋙ V ≅ U ⋙ F₂` with `U` and `V` exact and the derived unit
  `F₂.rightDerivedFunctorPlusUnit` is an isomorphism on `U`-images of bounded-below complexes of
  injectives (for example, whenever `U` sends injective objects into an `F₂`-adapted class, via
  `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_adapted`), then
  `F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ≅
    U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus`
  canonically and compatibly with shifts
  (`CategoryTheory.Functor.rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso`), inducing the
  cohomology comparison `CategoryTheory.Functor.rightDerivedFunctorPlusCompHomologyCompIso`.
* **Degree-zero recovery:** on complexes concentrated in degree `0`,
  `DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n`
  is naturally isomorphic to `F.rightDerived n` for every `n : ℕ`
  (`CategoryTheory.Functor.singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso`),
  compatibly with any injective resolution, and vanishes in negative degrees
  (`CategoryTheory.Functor.isZero_homology_rightDerivedFunctorPlus_singleFunctor_zero_of_neg`).

## References

* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-! ### Exact-functor comparison for `rightDerivedFunctorPlus` -/

section ExactComparison

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [EnoughInjectives C₁]
  {D₁ : Type u₂} [Category.{v₂} D₁] [Abelian D₁] [HasDerivedCategory.{w₂} D₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂] [EnoughInjectives C₂]
  {D₂ : Type*} [Category* D₂] [Abelian D₂] [HasDerivedCategory D₂]
  (F₁ : C₁ ⥤ D₁) [F₁.Additive] (F₂ : C₂ ⥤ D₂) [F₂.Additive]
  (U : C₁ ⥤ C₂) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (V : D₁ ⥤ D₂) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : F₁ ⋙ V ≅ U ⋙ F₂)
  (hU : ∀ I : CochainComplex.Plus (InjectiveObject C₁),
    IsIso (F₂.rightDerivedFunctorPlusUnit.app
      (U.mapCochainComplexPlus.obj ((InjectiveObject.ι C₁).mapCochainComplexPlus.obj I))))

/-- Derived unit for `F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus`. -/
private def rightDerivedCompUnit₁ :
    F₁.mapCochainComplexPlus ⋙ V.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus :=
  whiskerLeft F₁.mapCochainComplexPlus V.mapDerivedCategoryPlusFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight F₁.rightDerivedFunctorPlusUnit V.mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom

private instance : NatTrans.CommShift (rightDerivedCompUnit₁ F₁ V) ℤ := by
  dsimp [rightDerivedCompUnit₁]
  infer_instance

/-- Derived unit for `U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus`, transported along
`e : F₁ ⋙ V ≅ U ⋙ F₂`. -/
private def rightDerivedCompUnit₂ :
    F₁.mapCochainComplexPlus ⋙ V.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight ((F₁.mapCochainComplexPlusCompIso V).hom ≫
      e.hom.mapCochainComplexPlus ≫ (U.mapCochainComplexPlusCompIso F₂).inv) _ ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft U.mapCochainComplexPlus F₂.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight U.mapDerivedCategoryPlusFactors.inv F₂.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

private instance : NatTrans.CommShift (rightDerivedCompUnit₂ F₁ F₂ U V e) ℤ := by
  have : NatTrans.CommShift (F₁.mapCochainComplexPlusCompIso V).hom ℤ := inferInstance
  have : NatTrans.CommShift e.hom.mapCochainComplexPlus ℤ := inferInstance
  have : NatTrans.CommShift (U.mapCochainComplexPlusCompIso F₂).inv ℤ := inferInstance
  dsimp [rightDerivedCompUnit₂]
  infer_instance

omit [HasDerivedCategory C₁] [EnoughInjectives C₁] in
private lemma localizerMorphism_derives_comp :
    (CochainComplex.Plus.localizerMorphism C₁).Derives
      (F₁.mapCochainComplexPlus ⋙ V.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  have : IsIso (DerivedCategory.Plus.Q.map (F₁.mapCochainComplexPlus.map
      ((InjectiveObject.ι C₁).mapCochainComplexPlus.map f))) :=
    CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F₁ f hf
  exact (NatIso.isIso_map_iff V.mapDerivedCategoryPlusFactors
    (F₁.mapCochainComplexPlus.map ((InjectiveObject.ι C₁).mapCochainComplexPlus.map f))).1
    (inferInstanceAs (IsIso (V.mapDerivedCategoryPlus.map _)))

private lemma isRightDerivedFunctor_comp₁ :
    (F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (rightDerivedCompUnit₁ F₁ V) (CochainComplex.Plus.quasiIso C₁) :=
  (localizerMorphism_derives_comp F₁ V).isRightDerivedFunctor_of_isIso _ fun I ↦ by
    dsimp [rightDerivedCompUnit₁]
    infer_instance

include hU in
private lemma isRightDerivedFunctor_comp₂ :
    (U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedCompUnit₂ F₁ F₂ U V e) (CochainComplex.Plus.quasiIso C₁) :=
  (localizerMorphism_derives_comp F₁ V).isRightDerivedFunctor_of_isIso _ fun I ↦ by
    have := hU I
    dsimp [rightDerivedCompUnit₂]
    infer_instance

include hU in
/-- **Exact-functor comparison for bounded-below right derived functors.**
If `F₁ ⋙ V ≅ U ⋙ F₂` with `U` and `V` exact and `F₂.rightDerivedFunctorPlusUnit` is an
isomorphism on `U`-images of bounded-below complexes of injectives (for instance, when `U` sends
injectives into an `F₂`-adapted class), then `RF₁⁺ ⋙ V⁺ ≅ U⁺ ⋙ RF₂⁺` canonically and
compatibly with shifts. -/
def rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso :
    F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ≅
      U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus :=
  have := isRightDerivedFunctor_comp₁ F₁ V
  have := isRightDerivedFunctor_comp₂ F₁ F₂ U V e hU
  Functor.rightDerivedUnique
    (F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus)
    (U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus)
    (rightDerivedCompUnit₁ F₁ V) (rightDerivedCompUnit₂ F₁ F₂ U V e)
    (CochainComplex.Plus.quasiIso C₁)

include hU in
/-- Universal-property characterization of `rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso`:
it intertwines `F₁.rightDerivedFunctorPlusUnit` and `F₂.rightDerivedFunctorPlusUnit` along
`e : F₁ ⋙ V ≅ U ⋙ F₂`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso_hom_fac_app
    (K : CochainComplex.Plus C₁) :
    V.mapDerivedCategoryPlus.map (F₁.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso F₁ F₂ U V e hU).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      V.mapDerivedCategoryPlusFactors.hom.app (F₁.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map
          ((F₁.mapCochainComplexPlusCompIso V).hom.app K ≫
            e.hom.mapCochainComplexPlus.app K ≫
            (U.mapCochainComplexPlusCompIso F₂).inv.app K) ≫
        F₂.rightDerivedFunctorPlusUnit.app (U.mapCochainComplexPlus.obj K) ≫
        F₂.rightDerivedFunctorPlus.map (U.mapDerivedCategoryPlusFactors.inv.app K) := by
  have := isRightDerivedFunctor_comp₁ F₁ V
  have := isRightDerivedFunctor_comp₂ F₁ F₂ U V e hU
  rw [← cancel_epi (V.mapDerivedCategoryPlusFactors.inv.app (F₁.mapCochainComplexPlus.obj K)),
    Iso.inv_hom_id_app_assoc]
  have h := Functor.rightDerivedNatTrans_app
    (F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus)
    (U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus)
    (rightDerivedCompUnit₁ F₁ V) (rightDerivedCompUnit₂ F₁ F₂ U V e)
    (CochainComplex.Plus.quasiIso C₁) (Iso.refl _).hom K
  simpa only [rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, rightDerivedCompUnit₁, rightDerivedCompUnit₂, Iso.refl_hom,
    NatTrans.id_app, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    Category.assoc] using h

include hU in
instance : NatTrans.CommShift
    (rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso F₁ F₂ U V e hU).hom ℤ := by
  have := isRightDerivedFunctor_comp₁ F₁ V
  have := isRightDerivedFunctor_comp₂ F₁ F₂ U V e hU
  exact NatTrans.CommShift.of_isRightDerivedFunctor
    (rightDerivedCompUnit₁ F₁ V) (rightDerivedCompUnit₂ F₁ F₂ U V e)
    (𝟙 _) (CochainComplex.Plus.quasiIso C₁)
    (by simp [rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso])

include hU in
/-- Cohomology-level comparison for `rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso`:
`Hᵐ(RF₁⁺(-)) ⋙ V ≅ U⁺ ⋙ Hᵐ(RF₂⁺(-))`. -/
def rightDerivedFunctorPlusCompHomologyCompIso (m : ℤ) :
    (F₁.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D₁ m) ⋙ V ≅
      U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D₂ m :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F₁.rightDerivedFunctorPlus
      (V.mapDerivedCategoryPlusCompHomologyFunctorIso m).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso F₁ F₂ U V e hU)
      (DerivedCategory.Plus.homologyFunctor D₂ m) ≪≫
    Functor.associator _ _ _

include hU in
/-- Component formula for `rightDerivedFunctorPlusCompHomologyCompIso`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompHomologyCompIso_hom_app (m : ℤ)
    (X : DerivedCategory.Plus C₁) :
    (rightDerivedFunctorPlusCompHomologyCompIso F₁ F₂ U V e hU m).hom.app X =
      (V.mapDerivedCategoryPlusCompHomologyFunctorIso m).inv.app
          (F₁.rightDerivedFunctorPlus.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor D₂ m).map
          ((rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso F₁ F₂ U V e hU).hom.app X) := by
  dsimp only [rightDerivedFunctorPlusCompHomologyCompIso]
  simp

end ExactComparison

/-! ### Degree-zero recovery of classical right derived functors -/

section DegreeZero

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- Component isomorphism identifying `Hⁿ(RF⁺(X[0]))` with `(F.rightDerived n).obj X` via any
injective resolution `I` of `X`. -/
private def degreeZeroComponent (n : ℕ) (X : C) (I : InjectiveResolution X) :
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      (F.rightDerived n).obj X :=
  (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      (F.rightDerivedFunctorPlus.mapIso
        ((TauCeti.DerivedCategory.Plus.singleFunctorIsoCompQ C 0).app X)) ≪≫
    F.rightDerivedFunctorPlusHomologyObjIsoOfResolution I.extendResolution (n : ℤ) ≪≫
    HomologicalComplex.homologyMapIso
      (HomologicalComplex.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat) (n : ℤ) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n) ≪≫
    (I.isoRightDerivedObj F n).symm

private lemma degreeZeroComponent_hom (n : ℕ) (X : C) (I : InjectiveResolution X) :
    (degreeZeroComponent F n X I).hom =
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map
            ((TauCeti.DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.app X)) ≫
        (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution I.extendResolution (n : ℤ)).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).hom (n : ℤ) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
        (I.isoRightDerivedObj F n).inv :=
  rfl

/-- Naturality of `degreeZeroComponent` for any morphism `f : X ⟶ Y` and any choices of injective
resolutions `IX` and `IY`. -/
private lemma degreeZeroComponent_hom_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (IX : InjectiveResolution X) (IY : InjectiveResolution Y) :
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
        (degreeZeroComponent F n Y IY).hom =
      (degreeZeroComponent F n X IX).hom ≫ (F.rightDerived n).map f := by
  let φ : IX.cocomplex ⟶ IY.cocomplex := InjectiveResolution.desc f IY IX
  let φExt :
      (⟨IX.cocomplex.extend ComplexShape.embeddingUpNat,
          (CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩ : CochainComplex.Plus C) ⟶
      ⟨IY.cocomplex.extend ComplexShape.embeddingUpNat,
        (CochainComplex.plus_iff C _).2 ⟨0, inferInstance⟩⟩ :=
    ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  have h1 := congrArg (fun g ↦ (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
      (F.rightDerivedFunctorPlus.map g))
    ((TauCeti.DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.naturality f)
  simp only [Functor.map_comp] at h1
  have h2 := F.rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom_naturality
    IX.extendResolution IY.extendResolution
    ((TauCeti.CochainComplex.Plus.singleFunctor C 0).map f) φExt
    (InjectiveResolution.extendResolution_naturality f IX IY φ
      (InjectiveResolution.desc_commutes f IY IX)) (n : ℤ)
  have h3 := congrArg (fun g ↦ HomologicalComplex.homologyMap g (n : ℤ))
    (HomologicalComplex.mapExtendIso_hom_naturality F ComplexShape.embeddingUpNat φ)
  simp only [HomologicalComplex.homologyMap_comp] at h3
  have h4 := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat
    (ComplexShape.embeddingUpNat_f n)
  have h5 : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n ≫
      (IY.isoRightDerivedObj F n).inv =
      (IX.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f :=
    (InjectiveResolution.isoRightDerivedObj_inv_naturality f IX IY φ
      (InjectiveResolution.desc_commutes_zero f IY IX) F n).symm
  rw [degreeZeroComponent_hom, degreeZeroComponent_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2]
  dsimp only [φExt, ObjectProperty.homMk_hom]
  rw [reassoc_of% h3, reassoc_of% h4, h5]

/-- **Degree-zero complexes recover classical right derived functors.** For every `n : ℕ`,
`DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
  DerivedCategory.Plus.homologyFunctor D n`
is naturally isomorphic to `F.rightDerived n`. -/
def singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D (n : ℤ) ≅
      F.rightDerived n :=
  NatIso.ofComponents
    (fun X ↦ degreeZeroComponent F n X (injectiveResolution X))
    (fun f ↦ degreeZeroComponent_hom_naturality F n f
      (injectiveResolution _) (injectiveResolution _))

/-- On any object `X : C`, `singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso` is
computed by any injective resolution `I : InjectiveResolution X`, compatibly with
`I.isoRightDerivedObj F n` and `F.rightDerivedFunctorPlusHomologyObjIsoOfResolution`. -/
@[reassoc]
lemma singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso_hom_app_comp_isoRightDerivedObj
    (n : ℕ) (X : C) (I : InjectiveResolution X) :
    (F.singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso n).hom.app X ≫
        (I.isoRightDerivedObj F n).hom =
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map
            ((TauCeti.DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.app X)) ≫
        (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution I.extendResolution (n : ℤ)).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).hom (n : ℤ) ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom := by
  have h := degreeZeroComponent_hom_naturality F n (𝟙 X) (injectiveResolution X) I
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at h
  dsimp only [singleFunctorZeroCompRightDerivedFunctorPlusCompHomologyIso,
    NatIso.ofComponents_hom_app]
  rw [← h, degreeZeroComponent_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Derived cohomology of a degree-zero complex vanishes in negative degrees. -/
theorem isZero_homology_rightDerivedFunctorPlus_singleFunctor_zero_of_neg
    (X : C) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) :=
  DerivedCategory.Plus.isZero_homology_of_isGE _ 0 m hm

end DegreeZero

end CategoryTheory.Functor
