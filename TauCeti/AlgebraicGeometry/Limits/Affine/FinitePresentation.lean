/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Descent of affine finitely presented schemes

An affine scheme of finite presentation over a cofiltered limit of affine schemes
is the base change of an affine scheme of finite presentation at a finite stage.
The proof reduces to descent of finitely presented algebras along filtered
colimits of commutative rings.

Reference: The Stacks Project, Lemma 32.10.1 (Tag 01ZM).
-/

public section

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  (diagram : Index ⥤ Scheme.{schemeUniverse}) (cone : Cone diagram) (limit : IsLimit cone)

/-- The affine object-descent construction for a diagram already written as spectra. -/
private lemma exists_isPullback_of_specDiagram [IsCofiltered Index]
    (diagram : Index ⥤ CommRingCatᵒᵖ) (cone : Cone (diagram ⋙ Scheme.Spec)) (limit : IsLimit cone)
    {sourceRing : CommRingCat.{schemeUniverse}} (sourceMap : Spec sourceRing ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] :
    ∃ (stage : Index) (stageScheme : Scheme.{schemeUniverse}) (_ : IsAffine stageScheme)
      (stageMap : stageScheme ⟶ Spec (diagram.obj stage).unop)
      (_ : LocallyOfFinitePresentation stageMap) (comparison : Spec sourceRing ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app stage) := by
  let ringCocone := colimit.cocone diagram.leftOp
  let specCone := Scheme.Spec.mapCone (coneOfCoconeLeftOp ringCocone)
  have specLimit : IsLimit specCone := isLimitOfPreserves Scheme.Spec
    (isLimitConeOfCoconeLeftOp _ (colimit.isColimit diagram.leftOp))
  let coneIso := limit.conePointUniqueUpToIso specLimit
  obtain ⟨ringMap, map_eq⟩ := Spec.map_surjective (sourceMap ≫ coneIso.hom)
  have : LocallyOfFinitePresentation (Spec.map ringMap) := by
    rw [map_eq]
    infer_instance
  obtain ⟨stage, stageRing, stageMap, stage_finitePresentation, comparison, pushout⟩ :=
    TauCeti.CommRingCat.exists_isPushout_of_finitePresentation
      diagram.leftOp ringCocone (colimit.isColimit diagram.leftOp) ringMap
      (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map ringMap)›)
  have square : IsPullback (Spec.map comparison) (sourceMap ≫ coneIso.hom)
      (Spec.map stageMap) (specCone.π.app stage.unop) := by
    rw [← map_eq]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _ pushout).flip
  refine ⟨stage.unop, Spec stageRing, inferInstance, Spec.map stageMap,
    HasRingHomProperty.Spec_iff.mpr stage_finitePresentation, Spec.map comparison, ?_⟩
  exact square.of_iso (Iso.refl _) (Iso.refl _) coneIso.symm (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [coneIso])


include limit in
/-- An affine scheme of finite presentation over a cofiltered limit of affine
schemes is obtained by base change from a finitely presented affine stage. -/
lemma _root_.CategoryTheory.Functor.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
    [IsCofiltered Index]
    [∀ index, IsAffine (diagram.obj index)]
    {sourceScheme : Scheme.{schemeUniverse}} [IsAffine sourceScheme]
    (sourceMap : sourceScheme ⟶ cone.pt) [LocallyOfFinitePresentation sourceMap] :
    ∃ (stage : Index) (stageScheme : Scheme.{schemeUniverse}) (_ : IsAffine stageScheme)
      (stageMap : stageScheme ⟶ diagram.obj stage) (_ : LocallyOfFinitePresentation stageMap)
      (comparison : sourceScheme ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app stage) := by
  have limitAffine : IsAffine cone.pt := Scheme.isAffine_of_isLimit cone limit
  wlog sourceIsSpectrum : ∃ sourceRing, sourceScheme = Spec sourceRing generalizing sourceScheme
  · obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
        comparison, square⟩ :=
      this (sourceScheme := Spec Γ(sourceScheme, ⊤))
        (sourceScheme.isoSpec.inv ≫ sourceMap) ⟨_, rfl⟩
    refine ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
      sourceScheme.isoSpec.hom ≫ comparison, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := sourceScheme.isoSpec.hom) (snd := sourceMap)
      (f := sourceScheme.isoSpec.inv ≫ sourceMap) (g := 𝟙 cone.pt) ⟨by simp⟩).paste_horiz square
  obtain ⟨sourceRing, rfl⟩ := sourceIsSpectrum
  wlog diagramIsSpec : ∃ ringDiagram : Index ⥤ CommRingCatᵒᵖ,
      diagram = ringDiagram ⋙ Scheme.Spec generalizing diagram
  · let affinization : diagram ⟶ diagram ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec :=
      diagram.whiskerLeft ΓSpec.adjunction.unit
    have componentIsomorphisms : ∀ index : Index, IsIso (affinization.app index) :=
      fun index ↦ IsAffine.affine
    have affinizationIsomorphism : IsIso affinization := NatIso.isIso_of_isIso_app affinization
    have affineStages : ∀ index : Index,
        IsAffine ((diagram ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj index) :=
      fun index ↦ inferInstanceAs (IsAffine (Spec _))
    have source_finitePresentation : @LocallyOfFinitePresentation (Spec sourceRing)
        ((Cone.postcompose (asIso affinization).hom).obj cone).pt sourceMap := ‹_›
    obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
        comparison, square⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso affinization) cone).symm limit)
        limitAffine sourceMap ⟨diagram ⋙ Scheme.Γ.rightOp, rfl⟩
    have : LocallyOfFinitePresentation (stageMap ≫ inv (affinization.app stage)) := by
      have := stage_finitePresentation
      infer_instance
    refine ⟨stage, stageScheme, stageAffine, stageMap ≫ inv (affinization.app stage),
      this, comparison, ?_⟩
    refine square.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (affinization.app stage)).symm
      (by simp) (Category.comp_id sourceMap) (by rfl) ?_
    -- The postcomposed cone has the original point and postcomposed projection.
    change (cone.π.app stage ≫ affinization.app stage) ≫ inv (affinization.app stage) =
      𝟙 _ ≫ cone.π.app stage
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (cone.π.app stage)).symm
  obtain ⟨diagram, rfl⟩ := diagramIsSpec
  exact exists_isPullback_of_specDiagram diagram cone limit sourceMap

end AlgebraicGeometry
