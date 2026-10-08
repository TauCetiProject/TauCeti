/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Comap

/-!
# Morphisms of presentation-limit pre-adic spaces

A continuous map of Huber rings carrying `A⁺` into `B⁺` induces a morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)`. This file packages the existing morphism of presentation-limit
structure presheaves as a morphism of pre-adic spaces. The main point is compatibility with the
canonical stalk valuations, proved on rational germs using base change for completed rational
localizations.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPresheafedSpaceComap`: the underlying morphism of
  presheafed spaces.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap`: the induced morphism of
  pre-adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti TauCeti.Huber TauCeti.Huber.PairOfDefinition

public section

namespace TauCeti.ValuationSpectrum

universe v
variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

variable {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {P' : PairOfDefinition B} {Bplus : Subring B}

/-- Pulling a rational-localization point back along the completed base-change map gives the
rational-localization point attached to the pulled-back valuation. -/
theorem comap_mapHom_rationalLocalizationPoint (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (p : Presentation P) (q : Presentation P') (hden : q.den = φ p.den)
    (hnum : ∀ t ∈ p.num, φ t ∈ q.num) (x : spa Bplus)
    (hx : x ∈ spaBasicOpen Bplus q.num q.den)
    (hy : spaComap φ hφ Aplus Bplus hplus x ∈ spaBasicOpen Aplus p.num p.den) :
    comap ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (p.mapHom φ hφ q hden hnum)).hom
      (rationalLocalizationPoint hP' q x hx) =
      rationalLocalizationPoint hP p (spaComap φ hφ Aplus Bplus hplus x) hy := by
  let _ := locUniformSpace P p.num p.den (Localization.Away p.den) p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den (Localization.Away q.den) q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let y := spaComap φ hφ Aplus Bplus hplus x
  change y ∈ spaBasicOpen Aplus p.num p.den at hy
  set w := (spaCompletedLocalizationHomeomorph P' Bplus hP' q.num q.den _
    q.hasDenominatorPower).symm ⟨x, mem_spaBasicOpen.mp hx⟩
  let σTop : TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) ⟶
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den)) :=
    eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm ≫
      (p.mapHom φ hφ q hden hnum).hom ≫
      eqToHom (completionLocObj_obj P' q.num q.den _ q.hasDenominatorPower)
  let σComm := (Presentation.completionLocObjCommRingCatIso p).inv ≫
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
      (p.mapHom φ hφ q hden hnum) ≫
    (Presentation.completionLocObjCommRingCatIso q).hom
  let σ : UniformSpace.Completion (Localization.Away p.den) →+*
      UniformSpace.Completion (Localization.Away q.den) := σComm.hom
  have hσσTop : σ = σTop.1 := by
    have hc : σComm = (forget₂ TopCommRingCat CommRingCat).map σTop := by
      simp only [σComm, σTop, Functor.map_comp,
        Functor.comp_map,
        Presentation.completionLocObjCommRingCatIso_inv,
        Presentation.completionLocObjCommRingCatIso_hom]
      rfl
    exact congrArg CommRingCat.Hom.hom hc
  have hσ : Continuous σ := hσσTop.symm ▸ σTop.2
  have hcomp : σ.comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) =
      (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower).comp φ := by
    have hTop :
        (⟨toCompletionLoc P p.num p.den _ p.hasDenominatorPower,
            continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩ :
          TopCommRingCat.of A ⟶
            TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den))) ≫ σTop =
        (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫
          (⟨toCompletionLoc P' q.num q.den _ q.hasDenominatorPower,
            continuous_toCompletionLoc P' q.num q.den _ q.hasDenominatorPower⟩ :
          TopCommRingCat.of B ⟶
            TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den))) := by
      have h := congrArg (fun k ↦ k ≫
        eqToHom (completionLocObj_obj P' q.num q.den _ q.hasDenominatorPower))
        (Presentation.toCompletionLocTopHom_comp_mapHom φ hφ p q hden hnum)
      rw [Presentation.toCompletionLocTopHom_eq, Presentation.toCompletionLocTopHom_eq] at h
      simpa only [σTop, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
        Category.comp_id] using h
    rw [hσσTop]
    exact congrArg Subtype.val hTop
  have hwx : comap (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower) w.1 = x := by
    have hw := spaCompletedLocalizationHomeomorph_apply P' Bplus hP' q.num q.den _
      q.hasDenominatorPower w
    rw [Homeomorph.apply_symm_apply] at hw
    have hxw := congrArg (fun z ↦ z.1.1) hw
    simp only [spaLocToRationalSubset_val, spaComapLoc_val] at hxw
    exact hxw.symm
  have hmem : comap σ w.1 ∈
      spa (completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower) := by
    refine comap_mem_spa_completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower σ hσ
      ((mem_spa_iff _ _).mp w.2).1 (fun a ha ↦ ?_) ?_
    · rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
      exact ((mem_spa_iff _ _).mp w.2).2 _
        (toCompletionLoc_mem_completedPlusSubring P' Bplus q.num q.den _
          q.hasDenominatorPower (hplus a ha))
    · rw [hcomp, comap_comp, Function.comp_apply, hwx]
      simpa only [y, spaComap_val] using mem_spaBasicOpen.mp hy
  have hcomap : comap (σ.comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower)) w.1 =
      y.1 := by
    rw [hcomp, comap_comp, Function.comp_apply, hwx]
    exact (spaComap_val φ hφ Aplus Bplus hplus x).symm
  have hpt :
      (spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
        p.hasDenominatorPower).symm ⟨y, mem_spaBasicOpen.mp hy⟩ = ⟨comap σ w.1, hmem⟩ := by
    rw [Homeomorph.symm_apply_eq]
    refine Subtype.ext (Subtype.ext ?_)
    rw [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, ← hcomap,
      spaComapLoc_val, comap_comp, Function.comp_apply]
  rw [rationalLocalizationPoint_def, rationalLocalizationPoint_def, hpt]
  have hc :
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (p.mapHom φ hφ q hden hnum) ≫
        (Presentation.completionLocObjCommRingCatIso q).hom =
      (Presentation.completionLocObjCommRingCatIso p).hom ≫ σComm := by
    simp only [σComm, Iso.hom_inv_id_assoc]
  exact (comap_hom_comap_hom
    ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
      (p.mapHom φ hφ q hden hnum))
    (Presentation.completionLocObjCommRingCatIso q).hom w.1).trans <|
    (congrArg (fun f ↦ comap f.hom w.1) hc).trans <|
      (comap_hom_comap_hom (Presentation.completionLocObjCommRingCatIso p).hom σComm w.1).symm

/-- The morphism of presentation-limit presheafed spaces induced contravariantly by a continuous
ring homomorphism preserving the chosen rings of integral elements. -/
@[expose] noncomputable def presentationLimitPresheafedSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace ⟶
      (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace where
  base := spaComapTopHom φ hφ hplus
  c := presentationLimitPresheafComap φ hφ hopen hplus hBplus hsheaf

private noncomputable def presentationLimitRingPresheafedSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    ({ carrier := TopCat.of ↥(spa Bplus)
       presheaf := presentationLimitPresheafInCommRingCat P' Bplus } :
      PresheafedSpace CommRingCat.{v}) ⟶
    ({ carrier := TopCat.of ↥(spa Aplus)
       presheaf := presentationLimitPresheafInCommRingCat P Aplus } :
      PresheafedSpace CommRingCat.{v}) where
  base := spaComapTopHom φ hφ hplus
  c := eqToHom (presentationLimitPresheafInCommRingCat_def P Aplus) ≫
    Functor.whiskerRight
      (presentationLimitPresheafComap φ hφ hopen hplus hBplus hsheaf)
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat) ≫
    eqToHom (by
      rw [presentationLimitPresheafInCommRingCat_def]
      rfl)

private theorem presentationLimitRingPresheafedSpaceComap_c_app
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) (U : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitRingPresheafedSpaceComap φ hφ hopen hplus hBplus hsheaf).c.app U =
      eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus U) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (presentationLimitComap φ hφ hopen hplus hBplus hsheaf U.unop) ≫
        eqToHom (presentationLimitPresheafInCommRingCat_obj P' Bplus _).symm := by
  dsimp only [presentationLimitRingPresheafedSpaceComap]
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app,
    Functor.whiskerRight_app, presentationLimitPresheafComap_app]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  cat_disch

/-- The underlying morphism of presheafed spaces preserves the canonical stalk valuations. -/
theorem presentationLimitPresheafedSpaceComap_stalkValuation
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) (x : spa Bplus) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).stalkValuation
        (spaComap φ hφ Aplus Bplus hplus x) =
      comap ((TauCeti.PreAdicSpace.toRingPresheafedSpaceHom
        (presentationLimitPresheafedSpaceComap φ hφ hopen hplus hAplus hBplus hP hP'
          hsheaf)).stalkMap x).hom
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) := by
  refine (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP
    (spaComap φ hφ Aplus Bplus hplus x)).trans ?_
  rw [presentationLimitPreAdicSpace_stalkValuation P' Bplus hBplus hP' x]
  change presentationLimitStalkValuation hAplus hP (spaComap φ hφ Aplus Bplus hplus x) =
    comap ((presentationLimitRingPresheafedSpaceComap φ hφ hopen hplus hBplus
      hsheaf).stalkMap x).hom
      (presentationLimitStalkValuation hBplus hP' x)
  let f := presentationLimitRingPresheafedSpaceComap (P := P) (P' := P') φ hφ hopen hplus
    hBplus hsheaf
  have hbase : f.base x = spaComap φ hφ Aplus Bplus hplus x := by
    apply Subtype.ext
    dsimp [f, presentationLimitRingPresheafedSpaceComap]
  cases hbase
  symm
  apply eq_presentationLimitStalkValuation (x := f.base x) hAplus hP
  intro p hp hy
  let i : PresentationIndex (P := P) Aplus (spaBasicOpen Aplus p.num p.den) :=
    ⟨p, hp, le_rfl⟩
  let q := (i.comap (P' := P') φ hφ hopen hplus).pres
  have hx : x ∈ spaBasicOpen Bplus q.num q.den := by
    rw [show spaBasicOpen Bplus q.num q.den =
      (Opens.map (spaComapTopHom φ hφ hplus)).obj
        (spaBasicOpen Aplus p.num p.den) by
      exact PresentationIndex.spaBasicOpen_map_pres φ hφ hopen hplus _ i]
    exact Opens.mem_map.mpr hy
  have hq : spaBasicOpen Bplus q.num q.den ≤
      (Opens.map f.base).obj (spaBasicOpen Aplus p.num p.den) := by
    dsimp only [f, presentationLimitRingPresheafedSpaceComap]
    exact (i.comap (P' := P') φ hφ hopen hplus).le_open
  have hgerm :
      presentationLimitRationalGerm hAplus p hp
          (f.base x) hy ≫ f.stalkMap x =
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
            (p.mapHom φ hφ q
              (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
                classical
                rw [PresentationIndex.map_pres_num]
                exact Finset.mem_image_of_mem φ ht)) ≫
          presentationLimitRationalGerm hBplus q
            (i.comap (P' := P') φ hφ hopen hplus).isOpen_span x hx := by
    rw [presentationLimitRationalGerm_def, presentationLimitRationalGerm_def]
    rw [Category.assoc]
    have hsm := PresheafedSpace.stalkMap_germ f (spaBasicOpen Aplus p.num p.den) x hy
    rw [hsm]
    have hcTop :
        (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
            presentationLimitComap φ hφ hopen hplus hBplus hsheaf
              (spaBasicOpen Aplus p.num p.den) ≫
            presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open =
          p.mapHom φ hφ q
              (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
                classical
                rw [PresentationIndex.map_pres_num]
                exact Finset.mem_image_of_mem φ ht) ≫
            (presentationLimitRationalIso Bplus hBplus q
              (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).inv := by
      rw [← cancel_mono (presentationLimitRationalIso Bplus hBplus q
        (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [presentationLimitComap_comp_map_comp_hom]
      simp only [← Category.assoc, presentationLimitRationalIso_inv_comp_π,
        homOfRationalSubsetSubset_self, Category.id_comp]
      rfl
    have hc :
        (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫
            f.c.app (Opposite.op (spaBasicOpen Aplus p.num p.den)) ≫
            (presentationLimitPresheafInCommRingCat P' Bplus).map
              (homOfLE hq).op =
          (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
            (p.mapHom φ hφ q
              (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
                classical
                rw [PresentationIndex.map_pres_num]
                exact Finset.mem_image_of_mem φ ht)) ≫
            (presentationLimitRationalIsoInCommRingCat hBplus q
              (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).inv := by
      rw [show f.c.app (Opposite.op (spaBasicOpen Aplus p.num p.den)) = _ from by
        simpa only [f] using
          presentationLimitRingPresheafedSpaceComap_c_app
            φ hφ hopen hplus hBplus hsheaf
              (Opposite.op (spaBasicOpen Aplus p.num p.den))]
      dsimp only [f, presentationLimitRingPresheafedSpaceComap] at hq ⊢
      rw [← cancel_mono (presentationLimitRationalIsoInCommRingCat hBplus q
        (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [presentationLimitRationalIsoInCommRingCat_hom]
      rw [reassoc_of% presentationLimitPresheafInCommRingCat_map P' Bplus
        (homOfLE hq).op]
      have hcTop' :
          (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
              presentationLimitComap φ hφ hopen hplus hBplus hsheaf
                (spaBasicOpen Aplus p.num p.den) ≫
              presentationLimitMap (i.comap (P' := P') φ hφ hopen hplus).le_open ≫
              (presentationLimitRationalIso Bplus hBplus q
                (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).hom =
            p.mapHom φ hφ q
              (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
                classical
                rw [PresentationIndex.map_pres_num]
                exact Finset.mem_image_of_mem φ ht) := by
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using congrArg
          (fun k ↦ k ≫ (presentationLimitRationalIso Bplus hBplus q
            (i.comap (P' := P') φ hφ hopen hplus).isOpen_span).hom) hcTop
      simpa only [presentationLimitRationalIsoInCommRingCat_inv,
        Functor.comp_map, Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
        eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using congrArg
          (fun k ↦ (TopCommRingCat.isCompleteSeparated.ι ⋙
            forget₂ TopCommRingCat CommRingCat).map k) hcTop'
    rw [← (presentationLimitPresheafInCommRingCat P' Bplus).germ_res
      (homOfLE hq) x hx]
    with_unfolding_all rw [reassoc_of% hc]
    rfl
  rw [comap_hom_comap_hom, hgerm, ← comap_hom_comap_hom,
    comap_presentationLimitRationalGerm_presentationLimitStalkValuation]
  exact (show comap _ (rationalLocalizationPoint hP' q x hx) = _ from
    comap_mapHom_rationalLocalizationPoint φ hφ hplus hP hP' p q
      (PresentationIndex.map_pres_den φ hφ hopen hplus _ i) (fun t ht ↦ by
        classical
        rw [PresentationIndex.map_pres_num]
        exact Finset.mem_image_of_mem φ ht) x hx hy)

/-- The morphism of presentation-limit pre-adic spaces induced contravariantly by a continuous
ring homomorphism preserving the chosen rings of integral elements. -/
noncomputable def presentationLimitPreAdicSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP where
  toHom := presentationLimitPresheafedSpaceComap φ hφ hopen hplus hAplus hBplus hP hP'
    hsheaf
  stalkValuation_eq x :=
    presentationLimitPresheafedSpaceComap_stalkValuation φ hφ hopen hplus hAplus hBplus
      hP hP' hsheaf x

end TauCeti.ValuationSpectrum

end
