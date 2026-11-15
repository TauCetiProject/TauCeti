/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Functor.Shift
public import TauCeti.CategoryTheory.Shift.CommShift

/-!
# Natural transformations of stable functors commute with shifts

A natural transformation between exact functors preserving projective-injective objects
descends to the stable categories of Frobenius exact categories. Its components commute with
the canonical suspension comparisons and hence every integral shift. Thus shift compatibility
is natural in the original exact functor, not just in the objects of the stable category.
Install `stableNatTrans_commShift` locally after installing the stable shifts and the two
`stableFunctorCommShift` structures. It supplies Mathlib's `NatTrans.CommShift` interface,
including its natural-isomorphism and composition APIs.

The comparison is induced by morphisms of injective presentations. Naturality of the original
transformation supplies such a morphism, and independence of the extension to the middle terms
identifies its cokernel map in the stable quotient.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace TauCeti.StableConflationExact

open CategoryTheory CategoryTheory.Limits

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : ExactStructure C} {E' : ExactStructure D}
variable {F G : C ⥤ D} [F.Additive] [G.Additive]
variable (hF : StableConflationExact E E' F) (hG : StableConflationExact E E' G)
variable (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (α : F ⟶ G)

private theorem mapSuspensionPresentation_cokernelMap_natTrans (X : C) :
    E'.projectiveStableFunctor.map (α.app (hE.suspensionObj X)) ≫
        eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hG.mapSuspensionPresentation_K hE X).symm) =
      eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE X).symm) ≫
        E'.projectiveStableFunctor.map
          ((hF.mapSuspensionPresentation hE X).cokernelMap
            (hG.mapSuspensionPresentation hE X) (α.app X)) := by
  -- The presentation projections are opaque; the characteristic equalities transport
  -- the components of α to their middle and cokernel terms.
  let P := hF.mapSuspensionPresentation hE X
  let Q := hG.mapSuspensionPresentation hE X
  let a : P.I ⟶ Q.I := eqToHom (hF.mapSuspensionPresentation_I hE X) ≫
    α.app (hE.suspensionInjective X) ≫ eqToHom (hG.mapSuspensionPresentation_I hE X).symm
  let g : P.K ⟶ Q.K := eqToHom (hF.mapSuspensionPresentation_K hE X) ≫
    α.app (hE.suspensionObj X) ≫ eqToHom (hG.mapSuspensionPresentation_K hE X).symm
  have hiF := (conj_eqToHom_iff_heq _ _ rfl
    (hF.mapSuspensionPresentation_I hE X)).2 (hF.mapSuspensionPresentation_i hE X)
  have hiG := (conj_eqToHom_iff_heq _ _ rfl
    (hG.mapSuspensionPresentation_I hE X)).2 (hG.mapSuspensionPresentation_i hE X)
  have hpF := (conj_eqToHom_iff_heq _ _ (hF.mapSuspensionPresentation_I hE X)
    (hF.mapSuspensionPresentation_K hE X)).2 (hF.mapSuspensionPresentation_p hE X)
  have hpG := (conj_eqToHom_iff_heq _ _ (hG.mapSuspensionPresentation_I hE X)
    (hG.mapSuspensionPresentation_K hE X)).2 (hG.mapSuspensionPresentation_p hE X)
  have ha : P.i ≫ a = α.app X ≫ Q.i := by
    simp only [a, P, Q, hiF, hiG, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [α.naturality_assoc]
  have hg : P.p ≫ g = a ≫ Q.p := by
    simp only [a, g, P, Q, hpF, hpG, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [α.naturality_assoc]
  have h := E'.projectiveStableFunctor_map_cokernelMap_eq P Q
    (hG.isProjective_I_mapSuspensionPresentation hE X) (α.app X) a g ha hg
  rw [h]
  simp [g, Functor.map_comp, eqToHom_map]

@[reassoc]
private theorem suspensionComparison_natTrans (X : C) :
    E'.projectiveStableFunctor.map (α.app (hE.suspensionObj X)) ≫
        eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hG.mapSuspensionPresentation_K hE X).symm) ≫
        (hE'.projectiveStableIsoSuspensionObj (hG.mapSuspensionPresentation hE X)).hom =
      eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE X).symm) ≫
        (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X)).hom ≫
        E'.projectiveStableFunctor.map
          ((hE'.suspensionPresentation (F.obj X)).cokernelMap
            (hE'.suspensionPresentation (G.obj X)) (α.app X)) := by
  rw [← Category.assoc, mapSuspensionPresentation_cokernelMap_natTrans,
    Category.assoc, hE'.projectiveStableIsoSuspensionObj_hom_naturality]

/-- The descended natural transformation commutes with the canonical suspension comparisons
of the two stable functors. -/
@[reassoc]
theorem stableNatTrans_suspension :
    (hF.stableSuspensionCompStableFunctorIso hE hE').hom ≫
        Functor.whiskerRight (stableNatTrans hF hG hE α) hE'.stableSuspension =
      Functor.whiskerLeft hE.stableSuspension (stableNatTrans hF hG hE α) ≫
        (hG.stableSuspensionCompStableFunctorIso hE hE').hom := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext X
  let τ := stableNatTrans hF hG hE α
  have happ (A : C) : τ.app (E.projectiveStableFunctor.obj A) =
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A) ≫
        E'.projectiveStableFunctor.map (α.app A) ≫
          eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE A).symm := by
    apply (cancel_epi
      (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A).symm)).1
    apply (cancel_mono
      (eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE A))).1
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id] using
      stableNatTrans_app_projectiveStableFunctor_obj hF hG hE α A
  have hnat := τ.naturality
    (eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj X))
  dsimp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [stableSuspensionCompStableFunctorIso_hom_app,
    stableSuspensionCompStableFunctorIso_hom_app, happ]
  simp only [eqToHom_map] at hnat
  rw [← reassoc_of% hnat, happ]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp,
    ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map]
  rw [suspensionComparison_natTrans_assoc hF hG hE hE' α]
  simp only [eqToHom_trans_assoc]

/-- A descended natural transformation is compatible with all integral shifts of the stable
categories, for the canonical shift comparisons of the two stable functors. -/
theorem stableNatTrans_commShift :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hF.stableFunctorCommShift hE hE'
    letI := hG.stableFunctorCommShift hE hE'
    (stableNatTrans hF hG hE α).CommShift ℤ := by
  let _ := hE.stableHasShift
  let _ := hE'.stableHasShift
  let _ := hF.stableFunctorCommShift hE hE'
  let _ := hG.stableFunctorCommShift hE hE'
  apply natTrans_commShift_iff_one.mpr
  constructor
  ext X
  have hs := congr_app (stableNatTrans_suspension hF hG hE hE' α) X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs ⊢
  rw [hF.stableFunctorCommShift_iso_one hE hE',
    hG.stableFunctorCommShift_iso_one hE hE']
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  rw [← hE'.stableShiftFunctorOneIso.inv.naturality, reassoc_of% hs,
    (stableNatTrans hF hG hE α).naturality_assoc]

end TauCeti.StableConflationExact
