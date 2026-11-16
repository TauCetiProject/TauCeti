/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.RightDerived

/-!
# Comparison theorems for bounded-below right derived functors

This file proves two comparison theorems for Mathlib's bounded-below right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`:

* **Exact-functor comparison:** if `F₁ ⋙ V ≅ U ⋙ F₂` with `U` and `V` exact and `U` sends
  injective objects into an `F₂`-adapted class, then
  `F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ≅
    U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus`
  canonically and compatibly with shifts
  (`CategoryTheory.Functor.rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso`), inducing the
  cohomology comparison `CategoryTheory.Functor.rightDerivedFunctorPlusCompHomologyCompIso`.
* **Degree-zero recovery:** on complexes concentrated in degree `0`,
  `Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D n` is naturally
  isomorphic to `F.rightDerived n` for every `n : ℕ`
  (`CategoryTheory.Functor.singleZeroCompRightDerivedFunctorPlusCompHomologyIso`), and vanishes in
  negative degrees
  (`CategoryTheory.Functor.isZero_homology_rightDerivedFunctorPlus_singleZero_of_neg`).

## References

* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated HomologicalComplex ZeroObject

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-! ### Exact-functor comparison for `rightDerivedFunctorPlus` -/

section ExactComparison

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  [EnoughInjectives C₁]
  {D₁ : Type u₂} [Category.{v₂} D₁] [Abelian D₁] [HasDerivedCategory.{w₂} D₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂] [EnoughInjectives C₂]
  {D₂ : Type*} [Category* D₂] [Abelian D₂] [HasDerivedCategory D₂]

/-- Natural isomorphism `(F ⋙ G).mapCochainComplexPlus ≅ F.mapCochainComplexPlus ⋙
G.mapCochainComplexPlus`, compatible with shifts. -/
private def mapCochainComplexPlusCompIso {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] :
    (F ⋙ G).mapCochainComplexPlus ≅ F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Iso.refl _)) (fun _ ↦ by ext; simp)

private instance {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] :
    NatTrans.CommShift (mapCochainComplexPlusCompIso F G).hom ℤ :=
  NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι E) (by
    have h : Functor.whiskerRight (mapCochainComplexPlusCompIso F G).hom
          (CochainComplex.Plus.ι E) =
        (F ⋙ G).mapCochainComplexPlusCompι.hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A)
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight F.mapCochainComplexPlusCompι.inv (G.mapHomologicalComplex _) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft F.mapCochainComplexPlus G.mapCochainComplexPlusCompι.inv ≫
          (Functor.associator _ _ _).inv := by
      ext K n
      simp [mapCochainComplexPlusCompIso]
    rw [h]
    infer_instance)

variable (F₁ : C₁ ⥤ D₁) [F₁.Additive] (F₂ : C₂ ⥤ D₂) [F₂.Additive]
  (U : C₁ ⥤ C₂) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (V : D₁ ⥤ D₂) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : F₁ ⋙ V ≅ U ⋙ F₂)
  (P₂ : ObjectProperty C₂) [P₂.IsClosedUnderIsomorphisms]
  (hinj₂ : ∀ (Y : C₂), Injective Y → P₂ Y)
  (hP₂ : ∀ S : ShortComplex C₂, S.ShortExact → P₂ S.X₁ → P₂ S.X₂ → P₂ S.X₃)
  (hF₂ : ∀ S : ShortComplex C₂, S.ShortExact → P₂ S.X₁ → P₂ S.X₂ →
    (S.map F₂).ShortExact)
  (hU : ∀ (I : C₁), Injective I → P₂ (U.obj I))

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
    whiskerRight ((mapCochainComplexPlusCompIso F₁ V).inv ≫
      e.hom.mapCochainComplexPlus ≫ (mapCochainComplexPlusCompIso U F₂).hom) _ ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft U.mapCochainComplexPlus F₂.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight U.mapDerivedCategoryPlusFactors.inv F₂.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

private instance : NatTrans.CommShift (rightDerivedCompUnit₂ F₁ F₂ U V e) ℤ := by
  have : NatTrans.CommShift (mapCochainComplexPlusCompIso F₁ V).inv ℤ := inferInstance
  have : NatTrans.CommShift e.hom.mapCochainComplexPlus ℤ := inferInstance
  have : NatTrans.CommShift (mapCochainComplexPlusCompIso U F₂).hom ℤ := inferInstance
  dsimp [rightDerivedCompUnit₂]
  infer_instance

omit [HasDerivedCategory C₁] [EnoughInjectives C₁] in
private lemma localizerMorphism_derives_comp :
    (CochainComplex.Plus.localizerMorphism C₁).Derives
      (F₁.mapCochainComplexPlus ⋙ V.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  intro K L f hf
  have h1 : IsIso (DerivedCategory.Plus.Q.map (F₁.mapCochainComplexPlus.map
      ((InjectiveObject.ι C₁).mapCochainComplexPlus.map f))) :=
    CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F₁ f hf
  have hnat := V.mapDerivedCategoryPlusFactors.hom.naturality
    (F₁.mapCochainComplexPlus.map ((InjectiveObject.ι C₁).mapCochainComplexPlus.map f))
  dsimp at hnat ⊢
  have : IsIso (V.mapDerivedCategoryPlusFactors.hom.app _ ≫
      DerivedCategory.Plus.Q.map (V.mapCochainComplexPlus.map
        (F₁.mapCochainComplexPlus.map
          ((InjectiveObject.ι C₁).mapCochainComplexPlus.map f)))) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left (V.mapDerivedCategoryPlusFactors.hom.app _) _

private lemma isRightDerivedFunctor_comp₁ :
    (F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (rightDerivedCompUnit₁ F₁ V) (CochainComplex.Plus.quasiIso C₁) :=
  (localizerMorphism_derives_comp F₁ V).isRightDerivedFunctor_of_isIso _ fun I ↦ by
    dsimp [rightDerivedCompUnit₁]
    infer_instance

include hinj₂ hP₂ hF₂ hU in
private lemma isRightDerivedFunctor_comp₂ :
    (U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedCompUnit₂ F₁ F₂ U V e) (CochainComplex.Plus.quasiIso C₁) :=
  (localizerMorphism_derives_comp F₁ V).isRightDerivedFunctor_of_isIso _ fun I ↦ by
    have : IsIso (F₂.rightDerivedFunctorPlusUnit.app
        (U.mapCochainComplexPlus.obj ((InjectiveObject.ι C₁).mapCochainComplexPlus.obj I))) :=
      F₂.isIso_rightDerivedFunctorPlusUnit_app_of_adapted P₂ hinj₂ hP₂ hF₂ _ fun n ↦
        hU ((I.obj.X n).obj) (I.obj.X n).property
    have : IsIso (e.hom.mapCochainComplexPlus.app
        ((InjectiveObject.ι C₁).mapCochainComplexPlus.obj I)) := by
      refine ⟨e.inv.mapCochainComplexPlus.app _, ?_, ?_⟩
      · rw [← NatTrans.comp_app, ← NatTrans.mapCochainComplexPlus_comp, Iso.hom_inv_id,
          NatTrans.mapCochainComplexPlus_id, NatTrans.id_app]
      · rw [← NatTrans.comp_app, ← NatTrans.mapCochainComplexPlus_comp, Iso.inv_hom_id,
          NatTrans.mapCochainComplexPlus_id, NatTrans.id_app]
    dsimp [rightDerivedCompUnit₂]
    infer_instance

include hinj₂ hP₂ hF₂ hU in
/-- **Exact-functor comparison for bounded-below right derived functors.**
If `F₁ ⋙ V ≅ U ⋙ F₂` with `U` and `V` exact and `U` carries injective objects into an
`F₂`-adapted class `P₂`, then `RF₁⁺ ⋙ V⁺ ≅ U⁺ ⋙ RF₂⁺` canonically and compatibly with
shifts. -/
def rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso :
    F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ≅
      U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus :=
  have := isRightDerivedFunctor_comp₁ F₁ V
  have := isRightDerivedFunctor_comp₂ F₁ F₂ U V e P₂ hinj₂ hP₂ hF₂ hU
  Functor.rightDerivedUnique
    (F₁.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus)
    (U.mapDerivedCategoryPlus ⋙ F₂.rightDerivedFunctorPlus)
    (rightDerivedCompUnit₁ F₁ V) (rightDerivedCompUnit₂ F₁ F₂ U V e)
    (CochainComplex.Plus.quasiIso C₁)

include hinj₂ hP₂ hF₂ hU in
instance : NatTrans.CommShift
    (rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso
      F₁ F₂ U V e P₂ hinj₂ hP₂ hF₂ hU).hom ℤ := by
  have := isRightDerivedFunctor_comp₁ F₁ V
  have := isRightDerivedFunctor_comp₂ F₁ F₂ U V e P₂ hinj₂ hP₂ hF₂ hU
  exact NatTrans.CommShift.of_isRightDerivedFunctor
    (rightDerivedCompUnit₁ F₁ V) (rightDerivedCompUnit₂ F₁ F₂ U V e)
    (𝟙 _) (CochainComplex.Plus.quasiIso C₁)
    (by simp [rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso])

include hinj₂ hP₂ hF₂ hU in
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
      (rightDerivedFunctorPlusCompMapDerivedCategoryPlusIso
        F₁ F₂ U V e P₂ hinj₂ hP₂ hF₂ hU)
      (DerivedCategory.Plus.homologyFunctor D₂ m) ≪≫
    Functor.associator _ _ _

end ExactComparison

/-! ### Degree-zero recovery of classical right derived functors -/

section DegreeZero

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- Extending a `ℕ`-indexed cochain complex along `ComplexShape.embeddingUpNat` gives an object of
`CochainComplex.Plus C`. -/
private abbrev extendUpNatPlus (K : CochainComplex C ℕ) : CochainComplex.Plus C :=
  ⟨K.extend ComplexShape.embeddingUpNat, ⟨0, inferInstance⟩⟩

private instance (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)] (m : ℤ) :
    Injective ((extendUpNatPlus K).obj.X m) := by
  by_cases h : 0 ≤ m
  · lift m to ℕ using h
    exact Injective.of_iso
      (K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl).symm inferInstance
  · have hz : IsZero ((K.extend ComplexShape.embeddingUpNat).X m) :=
      HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat m fun k hk ↦ by
        simp only [ComplexShape.embeddingUpNat_f] at hk
        omega
    exact Injective.of_iso (hz.isoZero).symm inferInstance

private lemma embeddingUpNat_f_toNat {m : ℤ} (h : 0 ≤ m) :
    ComplexShape.embeddingUpNat.f m.toNat = m :=
  Int.toNat_of_nonneg h

/-- `F` commutes with extension along `ComplexShape.embeddingUpNat`. -/
private def mapExtendUpNatIso (K : CochainComplex C ℕ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m ↦
      if h : 0 ≤ m then
        F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := m.toNat)
            (embeddingUpNat_f_toNat h)) ≪≫
          (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
            ComplexShape.embeddingUpNat (i := m.toNat) (embeddingUpNat_f_toNat h)).symm
      else
        have hz₁ : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)).X m) :=
          F.map_isZero (HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat m
            fun k hk ↦ by simp only [ComplexShape.embeddingUpNat_f] at hk; omega)
        have hz₂ : IsZero ((((F.mapHomologicalComplex (.up ℕ)).obj K).extend
            ComplexShape.embeddingUpNat).X m) :=
          HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat m
            fun k hk ↦ by simp only [ComplexShape.embeddingUpNat_f] at hk; omega
        hz₁.iso hz₂)
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      by_cases hi : 0 ≤ i
      · have hi' : 0 ≤ i + 1 := by omega
        dsimp
        simp only [hi, hi', ↓reduceDIte, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        have h1 := K.extend_d_eq ComplexShape.embeddingUpNat
          (i := i.toNat) (j := (i + 1).toNat)
          (embeddingUpNat_f_toNat hi) (embeddingUpNat_f_toNat hi')
        have h2 := ((F.mapHomologicalComplex (.up ℕ)).obj K).extend_d_eq
          ComplexShape.embeddingUpNat (i := i.toNat) (j := (i + 1).toNat)
          (embeddingUpNat_f_toNat hi) (embeddingUpNat_f_toNat hi')
        rw [h1, h2]
        simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
          Functor.mapHomologicalComplex_obj_d]
        rw [← F.map_comp_assoc (K.extendXIso ComplexShape.embeddingUpNat
            (embeddingUpNat_f_toNat hi')).inv,
          Iso.inv_hom_id, F.map_id, Category.id_comp]
      · have hz : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj
            (K.extend ComplexShape.embeddingUpNat)).X i) :=
          F.map_isZero (HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat i
            fun k hk ↦ by simp only [ComplexShape.embeddingUpNat_f] at hk; omega)
        exact hz.eq_of_src _ _)

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
private lemma mapExtendUpNatIso_hom_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap φ _) ≫
        (mapExtendUpNatIso F L).hom =
      (mapExtendUpNatIso F K).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ) _ := by
  refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
  by_cases h : 0 ≤ m
  · dsimp [mapExtendUpNatIso]
    simp only [h, ↓reduceDIte, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (embeddingUpNat_f_toNat h),
      HomologicalComplex.extendMap_f ((F.mapHomologicalComplex (.up ℕ)).map φ)
        ComplexShape.embeddingUpNat (embeddingUpNat_f_toNat h)]
    simp only [F.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Functor.mapHomologicalComplex_map_f]
    rw [← F.map_comp_assoc (L.extendXIso ComplexShape.embeddingUpNat
        (embeddingUpNat_f_toNat h)).inv,
      Iso.inv_hom_id, F.map_id, Category.id_comp]
  · have hz : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).X m) :=
      F.map_isZero (HomologicalComplex.isZero_extend_X K ComplexShape.embeddingUpNat m
        fun k hk ↦ by simp only [ComplexShape.embeddingUpNat_f] at hk; omega)
    exact hz.eq_of_src _ _

private lemma embeddingUpNat_f_zero_eq {m : ℤ} (h : m = 0) :
    ComplexShape.embeddingUpNat.f 0 = m := by
  simp [h]

/-- `singleFunctor C 0` on `CochainComplex.Plus C` as the `embeddingUpNat` extension of
`CochainComplex.single₀ C`. -/
private def singleZeroExtendIso (X : C) :
    ((CochainComplex.singleFunctor C 0).obj X) ≅
      ((CochainComplex.single₀ C).obj X).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m ↦
      if h : m = 0 then
        ((CochainComplex.singleFunctor C 0).obj X).XIsoOfEq h ≪≫
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 X ≪≫
          (HomologicalComplex.singleObjXSelf (.up ℕ) 0 X).symm ≪≫
          (((CochainComplex.single₀ C).obj X).extendXIso
            ComplexShape.embeddingUpNat (i := 0) (embeddingUpNat_f_zero_eq h)).symm
      else
        have hz₁ : IsZero (((CochainComplex.singleFunctor C 0).obj X).X m) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X m h
        have hz₂ : IsZero ((((CochainComplex.single₀ C).obj X).extend
            ComplexShape.embeddingUpNat).X m) := by
          by_cases hm : 0 ≤ m
          · lift m to ℕ using hm
            have hm0 : m ≠ 0 := by omega
            exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 X m hm0).of_iso
              (((CochainComplex.single₀ C).obj X).extendXIso ComplexShape.embeddingUpNat
                (i := m) rfl)
          · exact HomologicalComplex.isZero_extend_X _ _ m fun k hk ↦ by
              simp only [ComplexShape.embeddingUpNat_f] at hk; omega
        hz₁.iso hz₂)
    (fun i j hij ↦ by
      by_cases hi : i = 0
      · subst hi
        obtain rfl : (0 : ℤ) + 1 = j := hij
        have hz : IsZero ((((CochainComplex.single₀ C).obj X).extend
            ComplexShape.embeddingUpNat).X 1) :=
          (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 X 1 (by simp)).of_iso
            (((CochainComplex.single₀ C).obj X).extendXIso ComplexShape.embeddingUpNat
              (i := 1) rfl)
        exact hz.eq_of_tgt _ _
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi).eq_of_src _ _)

omit [HasDerivedCategory C] [EnoughInjectives C] in
private lemma singleZeroExtendIso_naturality {X Y : C} (f : X ⟶ Y) :
    (CochainComplex.singleFunctor C 0).map f ≫ (singleZeroExtendIso Y).hom =
      (singleZeroExtendIso X).hom ≫
        HomologicalComplex.extendMap ((CochainComplex.single₀ C).map f) _ := by
  refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
  by_cases h : m = 0
  · subst h
    simp only [HomologicalComplex.comp_f, singleZeroExtendIso,
      HomologicalComplex.Hom.isoOfComponents_hom_f, ↓reduceDIte,
      HomologicalComplex.XIsoOfEq_rfl, Iso.trans_hom, Iso.refl_hom, Category.id_comp,
      Iso.symm_hom, Category.assoc]
    rw [HomologicalComplex.extendMap_f ((CochainComplex.single₀ C).map f)
      ComplexShape.embeddingUpNat (embeddingUpNat_f_zero_eq rfl)]
    dsimp only [CochainComplex.singleFunctor, CochainComplex.single₀]
    simp only [Iso.inv_hom_id_assoc, HomologicalComplex.single_map_f_self, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X m h).eq_of_src _ _

omit [HasDerivedCategory C] [EnoughInjectives C] in
private lemma quasiIso_extendMap_upNat {K L : CochainComplex C ℕ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) :=
  (HomologicalComplex.quasiIso_extendMap_iff f ComplexShape.embeddingUpNat).2 inferInstance

/-- The derived unit is an isomorphism on any bounded-below cochain complex of injectives. -/
private lemma isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (K : CochainComplex.Plus C) [∀ n, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  let L₀ : CochainComplex (InjectiveObject C) ℤ :=
    { X n := ⟨K.obj.X n, inferInstance⟩
      d i j := ObjectProperty.homMk (K.obj.d i j)
      shape i j hij := by ext; exact K.obj.shape i j hij
      d_comp_d' i j k _ _ := by ext; exact K.obj.d_comp_d i j k }
  let L : CochainComplex.Plus (InjectiveObject C) :=
    ⟨L₀, by
      obtain ⟨b, hb⟩ := K.property
      refine ⟨b, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact (IsZero.iff_id_eq_zero _).2 (by
        ext
        exact (K.obj.isZero_of_isStrictlyGE b i hi).eq_of_src _ _)⟩
  let eL : (InjectiveObject.ι C).mapCochainComplexPlus.obj L ≅ K :=
    ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
      (fun _ _ _ ↦ by simp [L, L₀]))
  have hnat := F.rightDerivedFunctorPlusUnit.naturality eL.hom
  dsimp at hnat
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map eL.hom) ≫
      F.rightDerivedFunctorPlusUnit.app K) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map eL.hom)) _

/-- `X` placed in degree `0`, as an object of `CochainComplex.Plus C`. -/
private abbrev singleZeroPlus (X : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩

/-- Helper isomorphism `(Plus.singleFunctor C 0).obj X ≅ Plus.Q.obj (singleZeroPlus X)`. -/
private def singleZeroPlusIso (X : C) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Q.obj (singleZeroPlus X) :=
  DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app X)

omit [EnoughInjectives C] in
private lemma singleZeroPlusIso_naturality {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫ (singleZeroPlusIso Y).hom =
      (singleZeroPlusIso X).hom ≫
        DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f) :
            singleZeroPlus X ⟶ singleZeroPlus Y) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hQ : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f) :
          singleZeroPlus X ⟶ singleZeroPlus Y)) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map f) := by
    have h := (DerivedCategory.Plus.QCompιIso C).hom.naturality
      (ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f) :
        singleZeroPlus X ⟶ singleZeroPlus Y)
    dsimp at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  have hmap (Z : C) : DerivedCategory.Plus.ι.map (singleZeroPlusIso Z).hom =
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app Z := by
    dsimp [singleZeroPlusIso]
    exact DerivedCategory.Plus.ι.map_preimage _
  rw [Functor.map_comp, Functor.map_comp, hmap Y, hmap X, hQ]
  exact (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality f

/-- Helper object isomorphism for degree-zero recovery via any injective resolution `I` of `X`. -/
private def singleZeroObjIso (X : C) (I : InjectiveResolution X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (extendUpNatPlus I.cocomplex)) := by
  let ι : singleZeroPlus X ⟶ extendUpNatPlus I.cocomplex :=
    ObjectProperty.homMk ((singleZeroExtendIso X).hom ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
  have : QuasiIso (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat) :=
    quasiIso_extendMap_upNat I.ι
  have : QuasiIso ι.hom := by
    change QuasiIso ((singleZeroExtendIso X).hom ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat)
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map ι) := DerivedCategory.Plus.isIso_Q_map_of_quasiIso ι
  have : IsIso (F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus I.cocomplex)) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_injective F (extendUpNatPlus I.cocomplex)
  exact F.rightDerivedFunctorPlus.mapIso (singleZeroPlusIso X) ≪≫
    F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus I.cocomplex))).symm

@[reassoc]
private lemma singleZeroObjIso_hom_comp_unit (X : C) (I : InjectiveResolution X) :
    (singleZeroObjIso F X I).hom ≫
        F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus I.cocomplex) =
      F.rightDerivedFunctorPlus.map
        ((singleZeroPlusIso X).hom ≫
          DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk ((singleZeroExtendIso X).hom ≫
              HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat) :
              singleZeroPlus X ⟶ extendUpNatPlus I.cocomplex)) := by
  have : IsIso (F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus I.cocomplex)) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_injective F (extendUpNatPlus I.cocomplex)
  dsimp [singleZeroObjIso]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Functor.map_comp]

/-- **Degree-zero complexes recover classical right derived functors.** For every `n : ℕ`,
`Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D n` is naturally
isomorphic to `F.rightDerived n`. -/
def singleZeroCompRightDerivedFunctorPlusCompHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D (n : ℤ) ≅
      F.rightDerived n :=
  NatIso.ofComponents
    (fun X ↦
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
          (singleZeroObjIso F X (injectiveResolution X)) ≪≫
        (DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).app _ ≪≫
        (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
          (mapExtendUpNatIso F (injectiveResolution X).cocomplex) ≪≫
        ((F.mapHomologicalComplex (.up ℕ)).obj
            (injectiveResolution X).cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n) ≪≫
        ((injectiveResolution X).isoRightDerivedObj F n).symm)
    (fun {X Y} f ↦ by
      set IX := injectiveResolution X
      set IY := injectiveResolution Y
      let φ : IX.cocomplex ⟶ IY.cocomplex := InjectiveResolution.desc f IY IX
      have hφ : IX.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ IY.ι :=
        InjectiveResolution.desc_commutes f IY IX
      let φExt : extendUpNatPlus IX.cocomplex ⟶ extendUpNatPlus IY.cocomplex :=
        ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
      -- Naturality of `singleZeroObjIso` with `φExt`.
      have hObj : F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
            (singleZeroObjIso F Y IY).hom =
          (singleZeroObjIso F X IX).hom ≫
            DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φExt) := by
        have hunitY : IsIso (F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus IY.cocomplex)) :=
          isIso_rightDerivedFunctorPlusUnit_app_of_injective F (extendUpNatPlus IY.cocomplex)
        rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app (extendUpNatPlus IY.cocomplex))]
        have hnat := F.rightDerivedFunctorPlusUnit.naturality φExt
        dsimp at hnat
        rw [Category.assoc, singleZeroObjIso_hom_comp_unit F Y IY,
          Category.assoc, hnat, singleZeroObjIso_hom_comp_unit_assoc F X IX]
        simp only [← Functor.map_comp]
        congr 1
        rw [← Category.assoc, singleZeroPlusIso_naturality f, Category.assoc,
          ← Functor.map_comp, Category.assoc, ← Functor.map_comp]
        congr 2
        apply (CochainComplex.Plus.ι C).map_injective
        refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
        change ((CochainComplex.singleFunctor C 0).map f ≫ (singleZeroExtendIso Y).hom ≫
            HomologicalComplex.extendMap IY.ι ComplexShape.embeddingUpNat).f m =
          (((singleZeroExtendIso X).hom ≫
            HomologicalComplex.extendMap IX.ι ComplexShape.embeddingUpNat) ≫
            HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f m
        rw [Category.assoc, ← HomologicalComplex.extendMap_comp, hφ,
          HomologicalComplex.extendMap_comp, ← Category.assoc, singleZeroExtendIso_naturality f,
          Category.assoc]
      let fac (Z : C) (I : InjectiveResolution Z) :
          (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
              (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj
                (extendUpNatPlus I.cocomplex))) ⟶
            ((F.mapHomologicalComplex (.up ℤ)).obj (extendUpNatPlus I.cocomplex).obj).homology
              (n : ℤ) :=
        ((DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).app
          (F.mapCochainComplexPlus.obj (extendUpNatPlus I.cocomplex))).hom
      have hHnat : (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
            (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φExt)) ≫ fac Y IY =
          fac X IX ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (.up ℤ)).map φExt.hom) (n : ℤ) :=
        (DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).hom.naturality
          (F.mapCochainComplexPlus.map φExt)
      have hExtNat : HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (.up ℤ)).map φExt.hom) (n : ℤ) ≫
            HomologicalComplex.homologyMap (mapExtendUpNatIso F IY.cocomplex).hom (n : ℤ) =
          HomologicalComplex.homologyMap (mapExtendUpNatIso F IX.cocomplex).hom (n : ℤ) ≫
            HomologicalComplex.homologyMap
              (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ)
                ComplexShape.embeddingUpNat) (n : ℤ) := by
        rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (.up ℤ)).map
              (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) ≫
              (mapExtendUpNatIso F IY.cocomplex).hom) (n : ℤ) = _
        rw [mapExtendUpNatIso_hom_naturality F φ]
      have hExtHom : HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map φ)
              ComplexShape.embeddingUpNat) (n : ℤ) ≫
            (((F.mapHomologicalComplex (.up ℕ)).obj IY.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom =
          (((F.mapHomologicalComplex (.up ℕ)).obj IX.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
            HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n :=
        HomologicalComplex.extendHomologyIso_hom_naturality
          ((F.mapHomologicalComplex (.up ℕ)).map φ) ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f n)
      let toRD (Z : C) (I : InjectiveResolution Z) :
          ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n ⟶
            (F.rightDerived n).obj Z :=
        (I.isoRightDerivedObj F n).inv
      have hRD' : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n ≫
            toRD Y IY =
          toRD X IX ≫ (F.rightDerived n).map f :=
        (InjectiveResolution.isoRightDerivedObj_inv_naturality f IX IY φ
          (InjectiveResolution.desc_commutes_zero f IY IX) F n).symm
      change (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
            (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
          ((DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map (singleZeroObjIso F Y IY).hom ≫
            fac Y IY ≫
            HomologicalComplex.homologyMap (mapExtendUpNatIso F IY.cocomplex).hom (n : ℤ) ≫
            (((F.mapHomologicalComplex (.up ℕ)).obj IY.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
            toRD Y IY) =
        ((DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map (singleZeroObjIso F X IX).hom ≫
          fac X IX ≫
          HomologicalComplex.homologyMap (mapExtendUpNatIso F IX.cocomplex).hom (n : ℤ) ≫
          (((F.mapHomologicalComplex (.up ℕ)).obj IX.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f n)).hom ≫
          toRD X IX) ≫ (F.rightDerived n).map f
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, hObj, Functor.map_comp_assoc,
        reassoc_of% hHnat, reassoc_of% hExtNat, reassoc_of% hExtHom, hRD'])

/-- Derived cohomology of a degree-zero complex vanishes in negative degrees. -/
theorem isZero_homology_rightDerivedFunctorPlus_singleZero_of_neg
    (X : C) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) := by
  let e := (DerivedCategory.Plus.homologyFunctor D m).mapIso
      (singleZeroObjIso F X (injectiveResolution X)) ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors D m).app _ ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) m).mapIso
      (mapExtendUpNatIso F (injectiveResolution X).cocomplex)
  have hex : (((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution X).cocomplex).extend
      ComplexShape.embeddingUpNat).ExactAt m :=
    HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat m fun k hk ↦ by
      simp only [ComplexShape.embeddingUpNat_f] at hk; omega
  exact hex.isZero_homology.of_iso e

end DegreeZero


end CategoryTheory.Functor
