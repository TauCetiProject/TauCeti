/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.CAff.RationalSite
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.IsSheafFor
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.OpenImmersion
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.OpenMapping
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport
import TauCeti.CategoryTheory.Sites.IsSheafForTrans

/-!
# Comparison between site-theoretic rational sheafiness and `Spa` structure presheaves

This file bridges the rational-covering site `(CAff.{u}ᵒᵖ, CAff.ratTopology)` with the
presentation-limit structure presheaf on `Spa(X)` (`presentationLimitPresheaf`).

## Main results

* `TauCeti.CAff.isSheafFor_globalSections_rationalCoverPresieve_iff`: `CAff.globalSections`
  satisfies `IsSheafFor` on a rational covering presieve of `Y` if and only if the underlying
  presheaf of sets of `presentationLimitPresheaf` on `Spa(Y)` satisfies `IsSheafFor` on the
  corresponding open cover.
* `TauCeti.CAff.IsRationalLocalization.isSheafyForEveryPresentation`: `IsSheafyForEveryPresentation`
  passes along any rational localization `φ : X ⟶ Y` in `CAff`.
* `TauCeti.CAff.IsRationalSheafy.of_isSheafyForEveryPresentation`: every topologically sheafy
  `X : CAff` is rational-sheafy.
* `TauCeti.CAff.isRationalSheafy_iff_isSheafyForEveryPresentation`: for a complete Hausdorff Tate
  Huber pair `X : CAff`, `X.IsRationalSheafy` is equivalent to topological sheafiness
  `IsSheafyForEveryPresentation X.pair.plus` (combining Wedhorn Remark 8.4 with Berkeley Lectures
  Proposition 4.3.4).

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §2–3 and §7.
* P. Scholze and J. Weinstein, *Berkeley Lectures on `p`-adic Geometry*, Annals of Mathematics
  Studies 207, Princeton University Press (2020), Proposition 4.3.4 and §4–5.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3, §8.1–8.2 (Lemma 8.1,
  Proposition 8.2, Remark 8.4).
-/

public section

open CategoryTheory Opposite TopologicalSpace Topology UniformSpace
open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.TopologicalSpace.Opens
open TauCeti.ValuationSpectrum

universe u

namespace TauCeti.CAff

private noncomputable def presentationLimitTopEquiv (Y : CAff.{u}) :
    Y.ring ≃
      presentationLimit (P := Y.pairOfDefinition) Y.pair.plus ⊤ :=
  ((forget _root_.TopCommRingCat).mapIso
    (eqToIso (CompleteSeparatedTopCommRingCat.of_obj Y.ring).symm) ≪≫
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat).mapIso
      (presentationLimitTopIso (P := Y.pairOfDefinition) Y.pair.plus
        Y.pair.isRingOfIntegralElements.isPowerBounded_of_mem).symm).toEquiv

private noncomputable def presentationLimitRationalEquiv (Y : CAff.{u})
    (q : Presentation Y.pairOfDefinition)
    (hq : IsOpen (Ideal.span (q.num : Set Y.ring) : Set Y.ring)) :
    presentationLimit (P := Y.pairOfDefinition) Y.pair.plus
        (spaBasicOpen Y.pair.plus q.num q.den) ≃
      (Y.rationalLocalization q.num q.den hq).ring :=
  let P := Y.pairOfDefinition
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  (Equiv.ofBijective _ (bijective_presentationLimitRationalIso_hom (P := P) Y.pair.plus
    Y.pair.isRingOfIntegralElements.isPowerBounded_of_mem q hq)).trans
    (Y.rationalLocalizationRingEquiv q.num q.den hq).toEquiv.symm

private theorem presentationLimitRationalEquiv_top (Y : CAff.{u})
    (T₀ : Finset Y.ring) (s₀ : Y.ring)
    (hT₀ : IsOpen (Ideal.span (T₀ : Set Y.ring) : Set Y.ring)) (b : Y.ring) :
    let P := Y.pairOfDefinition
    let q : Presentation P :=
      ⟨T₀, s₀, hasDenominatorPower_of_isOpen_span P T₀ s₀ (Localization.Away s₀) hT₀⟩
    presentationLimitRationalEquiv Y q hT₀
        ((presentationLimitMap (P := P)
          (le_top : spaBasicOpen Y.pair.plus T₀ s₀ ≤ ⊤)).hom.val
            (presentationLimitTopEquiv Y b)) =
      (Y.rationalLocalizationHom T₀ s₀ hT₀).toRingHom b := by
  let P := Y.pairOfDefinition
  let hAplus := Y.pair.isRingOfIntegralElements.isPowerBounded_of_mem
  let q : Presentation P :=
    ⟨T₀, s₀, hasDenominatorPower_of_isOpen_span P T₀ s₀ (Localization.Away s₀) hT₀⟩
  let _ := locUniformSpace P T₀ s₀ _ q.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P T₀ s₀ _ q.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P T₀ s₀ _ q.hasDenominatorPower
  refine (Y.rationalLocalizationRingEquiv T₀ s₀ hT₀).injective ?_
  rw [rationalLocalizationHom_toRingHom_apply]
  dsimp only [presentationLimitRationalEquiv]
  rw [Equiv.trans_apply]
  change (Y.rationalLocalizationRingEquiv T₀ s₀ hT₀).toEquiv
    ((Y.rationalLocalizationRingEquiv T₀ s₀ hT₀).toEquiv.symm _) = _
  rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply]
  have htop :
      (presentationLimitTopEquiv Y b :
        presentationLimit (P := P) Y.pair.plus ⊤) =
      (presentationLimitTopIso (P := P) Y.pair.plus hAplus).inv.hom.val
        ((eqToIso (CompleteSeparatedTopCommRingCat.of_obj Y.ring).symm).hom.val b) := rfl
  rw [htop, presentationLimitTopIso_inv]
  exact (rationalIso_map_top_apply Y.pair.plus hAplus q hT₀
      ((eqToIso (CompleteSeparatedTopCommRingCat.of_obj Y.ring).symm).hom.val b)).trans
    (congrArg (toCompletionLoc P q.num q.den _ q.hasDenominatorPower)
      ((eqToIso (CompleteSeparatedTopCommRingCat.of_obj Y.ring).symm).hom_inv_id_apply b))

private theorem presentationLimitRationalEquiv_restrict (Y : CAff.{u})
    {q₁ q₂ : Presentation Y.pairOfDefinition}
    (hq₁ : IsOpen (Ideal.span (q₁.num : Set Y.ring) : Set Y.ring))
    (hq₂ : IsOpen (Ideal.span (q₂.num : Set Y.ring) : Set Y.ring))
    (hsub : spaBasicOpen Y.pair.plus q₂.num q₂.den ≤ spaBasicOpen Y.pair.plus q₁.num q₁.den)
    (z : presentationLimit (P := Y.pairOfDefinition) Y.pair.plus
      (spaBasicOpen Y.pair.plus q₁.num q₁.den)) :
    (rationalLocalizationRestrict hq₁ hq₂ (spaBasicOpen_le_spaBasicOpen_iff.mp hsub)).toRingHom
        (presentationLimitRationalEquiv Y q₁ hq₁ z) =
      presentationLimitRationalEquiv Y q₂ hq₂
        ((presentationLimitMap (P := Y.pairOfDefinition) hsub).hom.val z) := by
  let P := Y.pairOfDefinition
  let hAplus := Y.pair.isRingOfIntegralElements.isPowerBounded_of_mem
  let _ := locUniformSpace P q₁.num q₁.den _ q₁.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P q₁.num q₁.den _ q₁.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P q₁.num q₁.den _ q₁.hasDenominatorPower
  let _ := locUniformSpace P q₂.num q₂.den _ q₂.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P q₂.num q₂.den _ q₂.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P q₂.num q₂.den _ q₂.hasDenominatorPower
  refine (Y.rationalLocalizationRingEquiv q₂.num q₂.den hq₂).injective ?_
  rw [rationalLocalizationRestrict_toRingHom_apply]
  dsimp only [presentationLimitRationalEquiv]
  rw [Equiv.trans_apply, Equiv.trans_apply]
  change ringHomOfRationalSubsetSubset _ _ _ _ _ _ _ _ _ _ _ _
      ((Y.rationalLocalizationRingEquiv q₁.num q₁.den hq₁).toEquiv
        ((Y.rationalLocalizationRingEquiv q₁.num q₁.den hq₁).toEquiv.symm _)) =
    (Y.rationalLocalizationRingEquiv q₂.num q₂.den hq₂).toEquiv
      ((Y.rationalLocalizationRingEquiv q₂.num q₂.den hq₂).toEquiv.symm _)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat
  have hEq := congrArg (fun f ↦ F.map (presentationLimitRationalIso Y.pair.plus hAplus q₁ hq₁).hom ≫
      F.map f ≫ q₂.completionLocObjCommRingCatIso.hom)
    (presentationLimitRationalIso_inv_comp_map_comp_hom Y.pair.plus hAplus q₁ q₂ hq₁ hq₂ hsub)
  rw [← F.map_comp_assoc, Iso.hom_inv_id_assoc, F.map_comp, Category.assoc,
    map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom hAplus
      (spaBasicOpen_le_spaBasicOpen_iff.mp hsub)] at hEq
  have hz := congrArg (fun f : F.obj _ ⟶ CommRingCat.of _ ↦
    f.hom (z : ↑(F.obj (presentationLimit (P := P) Y.pair.plus
      (spaBasicOpen Y.pair.plus q₁.num q₁.den))))) hEq
  have hcomp_hom : ∀ (q : Presentation P)
      (hq : IsOpen (Ideal.span (q.num : Set Y.ring) : Set Y.ring)),
      let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
      let _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
      let _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
      (F.map (presentationLimitRationalIso Y.pair.plus hAplus q hq).hom ≫
        q.completionLocObjCommRingCatIso.hom).hom =
      (eqToHom (completionLocObj_obj P q.num q.den _ q.hasDenominatorPower)).val.comp
        (presentationLimitRationalIso Y.pair.plus hAplus q hq).hom.hom.val := fun q hq ↦ by
    let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
    let _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    let _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
    rw [CommRingCat.hom_comp, Presentation.completionLocObjCommRingCatIso_hom]
    rfl
  have hlhs_hom :
      (F.map (presentationLimitRationalIso Y.pair.plus hAplus q₁ hq₁).hom ≫
        q₁.completionLocObjCommRingCatIso.hom ≫
        CommRingCat.ofHom (ringHomOfRationalSubsetSubset P Y.pair.plus hAplus q₁.num q₁.den
          (Localization.Away q₁.den) q₁.hasDenominatorPower q₂.num q₂.den
          (Localization.Away q₂.den) q₂.hasDenominatorPower
          (spaBasicOpen_le_spaBasicOpen_iff.mp hsub))).hom =
      (ringHomOfRationalSubsetSubset P Y.pair.plus hAplus q₁.num q₁.den
        (Localization.Away q₁.den) q₁.hasDenominatorPower q₂.num q₂.den
        (Localization.Away q₂.den) q₂.hasDenominatorPower
        (spaBasicOpen_le_spaBasicOpen_iff.mp hsub)).comp
          ((eqToHom (completionLocObj_obj P q₁.num q₁.den _ q₁.hasDenominatorPower)).val.comp
            (presentationLimitRationalIso Y.pair.plus hAplus q₁ hq₁).hom.hom.val) := by
    rw [← Category.assoc, CommRingCat.hom_comp, CommRingCat.hom_ofHom, hcomp_hom q₁ hq₁]
    rfl
  have hrhs_hom :
      (F.map (presentationLimitMap (P := P) hsub) ≫
        F.map (presentationLimitRationalIso Y.pair.plus hAplus q₂ hq₂).hom ≫
        q₂.completionLocObjCommRingCatIso.hom).hom =
      ((eqToHom (completionLocObj_obj P q₂.num q₂.den _ q₂.hasDenominatorPower)).val.comp
        (presentationLimitRationalIso Y.pair.plus hAplus q₂ hq₂).hom.hom.val).comp
          (presentationLimitMap (P := P) hsub).hom.val := by
    rw [CommRingCat.hom_comp, hcomp_hom q₂ hq₂]
    rfl
  exact (congrArg (fun f : _ →+* _ ↦ f z) hlhs_hom).symm.trans
    (hz.symm.trans (congrArg (fun f : _ →+* _ ↦ f z) hrhs_hom))

private theorem rationalLocalization_compatible_iff (Y : CAff.{u})
    (T₁ T₂ T₁₂ : Finset Y.ring) (s₁ s₂ s₁₂ : Y.ring)
    (h₁ : IsOpen (Ideal.span (T₁ : Set Y.ring) : Set Y.ring))
    (h₂ : IsOpen (Ideal.span (T₂ : Set Y.ring) : Set Y.ring))
    (h₁₂ : IsOpen (Ideal.span (T₁₂ : Set Y.ring) : Set Y.ring))
    (hU₁₂ : spaBasicOpen Y.pair.plus T₁₂ s₁₂ =
      spaBasicOpen Y.pair.plus T₁ s₁ ⊓ spaBasicOpen Y.pair.plus T₂ s₂)
    (hinter : rationalSubset Y.pair.plus T₁₂ s₁₂ =
      rationalSubset Y.pair.plus T₁ s₁ ∩ rationalSubset Y.pair.plus T₂ s₂)
    [Limits.HasPullback (Y.rationalLocalizationHom T₁ s₁ h₁).op
      (Y.rationalLocalizationHom T₂ s₂ h₂).op]
    (hpull : IsPullback
      (rationalLocalizationRestrict h₁ h₁₂ (hinter.le.trans Set.inter_subset_left)).op
      (rationalLocalizationRestrict h₂ h₁₂ (hinter.le.trans Set.inter_subset_right)).op
      (Y.rationalLocalizationHom T₁ s₁ h₁).op
      (Y.rationalLocalizationHom T₂ s₂ h₂).op)
    (x₁ : presentationLimit (P := Y.pairOfDefinition) Y.pair.plus
      (spaBasicOpen Y.pair.plus T₁ s₁))
    (x₂ : presentationLimit (P := Y.pairOfDefinition) Y.pair.plus
      (spaBasicOpen Y.pair.plus T₂ s₂)) :
    let P := Y.pairOfDefinition
    let p₁ : Presentation P :=
      ⟨T₁, s₁, hasDenominatorPower_of_isOpen_span P T₁ s₁ (Localization.Away s₁) h₁⟩
    let p₂ : Presentation P :=
      ⟨T₂, s₂, hasDenominatorPower_of_isOpen_span P T₂ s₂ (Localization.Away s₂) h₂⟩
    globalSections.map (Limits.pullback.fst (Y.rationalLocalizationHom T₁ s₁ h₁).op
        (Y.rationalLocalizationHom T₂ s₂ h₂).op).op
      (presentationLimitRationalEquiv Y p₁ h₁ x₁) =
    globalSections.map (Limits.pullback.snd (Y.rationalLocalizationHom T₁ s₁ h₁).op
        (Y.rationalLocalizationHom T₂ s₂ h₂).op).op
      (presentationLimitRationalEquiv Y p₂ h₂ x₂) ↔
    (presentationLimitMap (P := P)
      (inf_le_left : spaBasicOpen Y.pair.plus T₁ s₁ ⊓ spaBasicOpen Y.pair.plus T₂ s₂ ≤
        spaBasicOpen Y.pair.plus T₁ s₁)).hom.val x₁ =
    (presentationLimitMap (P := P)
      (inf_le_right : spaBasicOpen Y.pair.plus T₁ s₁ ⊓ spaBasicOpen Y.pair.plus T₂ s₂ ≤
        spaBasicOpen Y.pair.plus T₂ s₂)).hom.val x₂ := by
  let P := Y.pairOfDefinition
  let p₁ : Presentation P :=
    ⟨T₁, s₁, hasDenominatorPower_of_isOpen_span P T₁ s₁ (Localization.Away s₁) h₁⟩
  let p₂ : Presentation P :=
    ⟨T₂, s₂, hasDenominatorPower_of_isOpen_span P T₂ s₂ (Localization.Away s₂) h₂⟩
  let p₁₂ : Presentation P :=
    ⟨T₁₂, s₁₂, hasDenominatorPower_of_isOpen_span P T₁₂ s₁₂ (Localization.Away s₁₂) h₁₂⟩
  have hiso : Function.Bijective (globalSections.map hpull.isoPullback.hom.op) :=
    ConcreteCategory.bijective_of_isIso _
  let y₁ : globalSections.obj (op (op (Y.rationalLocalization T₁ s₁ h₁))) :=
    presentationLimitRationalEquiv Y p₁ h₁ x₁
  let y₂ : globalSections.obj (op (op (Y.rationalLocalization T₂ s₂ h₂))) :=
    presentationLimitRationalEquiv Y p₂ h₂ x₂
  have hcomp₁ :
      globalSections.map hpull.isoPullback.hom.op
        (globalSections.map (Limits.pullback.fst (Y.rationalLocalizationHom T₁ s₁ h₁).op
          (Y.rationalLocalizationHom T₂ s₂ h₂).op).op y₁) =
      (rationalLocalizationRestrict h₁ h₁₂
        (hinter.le.trans Set.inter_subset_left)).toRingHom
          (presentationLimitRationalEquiv Y p₁ h₁ x₁) := by
    refine (Functor.map_comp_apply globalSections _ _ y₁).symm.trans ?_
    rw [← op_comp, hpull.isoPullback_hom_fst, globalSections_map_apply]
  have hcomp₂ :
      globalSections.map hpull.isoPullback.hom.op
        (globalSections.map (Limits.pullback.snd (Y.rationalLocalizationHom T₁ s₁ h₁).op
          (Y.rationalLocalizationHom T₂ s₂ h₂).op).op y₂) =
      (rationalLocalizationRestrict h₂ h₁₂
        (hinter.le.trans Set.inter_subset_right)).toRingHom
          (presentationLimitRationalEquiv Y p₂ h₂ x₂) := by
    refine (Functor.map_comp_apply globalSections _ _ y₂).symm.trans ?_
    rw [← op_comp, hpull.isoPullback_hom_snd, globalSections_map_apply]
  have hle₁ : spaBasicOpen Y.pair.plus T₁₂ s₁₂ ≤ spaBasicOpen Y.pair.plus T₁ s₁ :=
    hU₁₂.le.trans inf_le_left
  have hle₂ : spaBasicOpen Y.pair.plus T₁₂ s₁₂ ≤ spaBasicOpen Y.pair.plus T₂ s₂ :=
    hU₁₂.le.trans inf_le_right
  have hlhs :
      (rationalLocalizationRestrict h₁ h₁₂
          (hinter.le.trans Set.inter_subset_left)).toRingHom
            (presentationLimitRationalEquiv Y p₁ h₁ x₁) =
        presentationLimitRationalEquiv Y p₁₂ h₁₂
          ((presentationLimitMap (P := P) hle₁).hom.val x₁) :=
    presentationLimitRationalEquiv_restrict Y (q₁ := p₁) (q₂ := p₁₂) h₁ h₁₂ hle₁ x₁
  have hrhs :
      (rationalLocalizationRestrict h₂ h₁₂
          (hinter.le.trans Set.inter_subset_right)).toRingHom
            (presentationLimitRationalEquiv Y p₂ h₂ x₂) =
        presentationLimitRationalEquiv Y p₁₂ h₁₂
          ((presentationLimitMap (P := P) hle₂).hom.val x₂) :=
    presentationLimitRationalEquiv_restrict Y (q₁ := p₂) (q₂ := p₁₂) h₂ h₁₂ hle₂ x₂
  have hmap₁ :
      (presentationLimitMap (P := P) hle₁).hom.val x₁ =
        (presentationLimitMap (P := P) hU₁₂.le).hom.val
          ((presentationLimitMap (P := P) inf_le_left).hom.val x₁) := by
    rw [← presentationLimitMap_comp (P := P) inf_le_left hU₁₂.le]; rfl
  have hmap₂ :
      (presentationLimitMap (P := P) hle₂).hom.val x₂ =
        (presentationLimitMap (P := P) hU₁₂.le).hom.val
          ((presentationLimitMap (P := P) inf_le_right).hom.val x₂) := by
    rw [← presentationLimitMap_comp (P := P) inf_le_right hU₁₂.le]; rfl
  have h12 :
      (globalSections.map hpull.isoPullback.hom.op
          (globalSections.map (Limits.pullback.fst (Y.rationalLocalizationHom T₁ s₁ h₁).op
            (Y.rationalLocalizationHom T₂ s₂ h₂).op).op y₁) =
        globalSections.map hpull.isoPullback.hom.op
          (globalSections.map (Limits.pullback.snd (Y.rationalLocalizationHom T₁ s₁ h₁).op
            (Y.rationalLocalizationHom T₂ s₂ h₂).op).op y₂)) ↔
      (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Y.pair.plus T₁ s₁ ⊓ spaBasicOpen Y.pair.plus T₂ s₂ ≤
          spaBasicOpen Y.pair.plus T₁ s₁)).hom.val x₁ =
      (presentationLimitMap (P := P)
        (inf_le_right : spaBasicOpen Y.pair.plus T₁ s₁ ⊓ spaBasicOpen Y.pair.plus T₂ s₂ ≤
          spaBasicOpen Y.pair.plus T₂ s₂)).hom.val x₂ := by
    rw [hcomp₁, hcomp₂, hlhs, hrhs]
    refine ((presentationLimitRationalEquiv Y p₁₂ h₁₂).injective.eq_iff).trans ?_
    rw [hmap₁, hmap₂]
    have _ : IsIso (presentationLimitMap (P := P) hU₁₂.le) :=
      ⟨presentationLimitMap (P := P) hU₁₂.symm.le,
        by rw [presentationLimitMap_comp, presentationLimitMap_refl],
        by rw [presentationLimitMap_comp, presentationLimitMap_refl]⟩
    exact (ConcreteCategory.bijective_of_isIso
      (TopCommRingCat.isCompleteSeparated.ι.map
        (presentationLimitMap (P := P) hU₁₂.le))).injective.eq_iff
  exact hiso.injective.eq_iff.symm.trans h12

/-- **Gluing of `CAff.globalSections` on a rational covering presieve vs.
`presentationLimitPresheaf`.**
For *any* complete Hausdorff Huber pair `Y : CAff.{u}` (Tate or not) and any family of open-span
rational data `(T i, s i)` on `Y`, `CAff.globalSections` satisfies `Presieve.IsSheafFor` on
`Y.rationalCoverPresieve T s hT` if and only if the underlying presheaf of sets of
`presentationLimitPresheaf Y.pairOfDefinition Y.pair.plus` satisfies `Presieve.IsSheafFor` on the
family of rational opens `spaBasicOpen Y.pair.plus (T i) (s i) ≤ ⊤`. -/
theorem isSheafFor_globalSections_rationalCoverPresieve_iff (Y : CAff.{u}) {ι : Type*}
    (T : ι → Finset Y.ring) (s : ι → Y.ring)
    (hT : ∀ i, IsOpen (Ideal.span (T i : Set Y.ring) : Set Y.ring)) :
    Presieve.IsSheafFor globalSections (Y.rationalCoverPresieve T s hT) ↔
      (Presieve.ofArrows (fun i ↦ spaBasicOpen Y.pair.plus (T i) (s i))
        fun i ↦ homOfLE le_top).IsSheafFor
          (presentationLimitPresheaf Y.pairOfDefinition Y.pair.plus ⋙
            TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) := by
  let P := Y.pairOfDefinition
  let U (i : ι) : Opens ↥(ValuationSpectrum.spa Y.pair.plus) :=
    spaBasicOpen Y.pair.plus (T i) (s i)
  let mkPres (T₀ : Finset Y.ring) (s₀ : Y.ring)
      (hT₀ : IsOpen (Ideal.span (T₀ : Set Y.ring) : Set Y.ring)) : Presentation P :=
    ⟨T₀, s₀, hasDenominatorPower_of_isOpen_span P T₀ s₀ (Localization.Away s₀) hT₀⟩
  let p (i : ι) : Presentation P := mkPres (T i) (s i) (hT i)
  let eTop := presentationLimitTopEquiv Y
  let ePiece (i : ι) :
      presentationLimit (P := P) Y.pair.plus (U i) ≃
        (Y.rationalLocalization (T i) (s i) (hT i)).ring :=
    presentationLimitRationalEquiv Y (p i) (hT i)
  choose T' s' hT' hUij using fun i j ↦ mem_spaRationalOpens_iff_exists_spaBasicOpen.mp <|
    inf_mem_spaRationalOpens
      (show U i ∈ spaRationalOpens Y.pair.plus from spaBasicOpen_mem_spaRationalOpens (hT i))
      (show U j ∈ spaRationalOpens Y.pair.plus from spaBasicOpen_mem_spaRationalOpens (hT j))
  have hinter (i j : ι) :
      rationalSubset Y.pair.plus (T' i j) (s' i j) =
        rationalSubset Y.pair.plus (T i) (s i) ∩ rationalSubset Y.pair.plus (T j) (s j) := by
    refine le_antisymm (fun w hw ↦ ?_) (fun w ⟨hw₁, hw₂⟩ ↦ ?_)
    · have hw' : (⟨w, rationalSubset_subset_spa _ _ _ hw⟩ :
          ↥(ValuationSpectrum.spa Y.pair.plus)) ∈ U i ⊓ U j :=
        (hUij i j) ▸ mem_spaBasicOpen.mpr hw
      exact ⟨mem_spaBasicOpen.mp hw'.1, mem_spaBasicOpen.mp hw'.2⟩
    · exact mem_spaBasicOpen.mp <| (hUij i j) ▸
        (show (⟨w, rationalSubset_subset_spa _ _ _ hw₁⟩ :
          ↥(ValuationSpectrum.spa Y.pair.plus)) ∈ U i ⊓ U j from
          ⟨mem_spaBasicOpen.mpr hw₁, mem_spaBasicOpen.mpr hw₂⟩)
  have hpull (i j : ι) :=
    isPullback_rationalLocalizationRestrict (hT i) (hT j) (hT' i j) (hinter i j)
  have : (Presieve.ofArrows (fun i ↦ op (Y.rationalLocalization (T i) (s i) (hT i)))
      fun i ↦ (Y.rationalLocalizationHom (T i) (s i) (hT i)).op).HasPairwisePullbacks :=
    ⟨by rintro _ _ _ ⟨i⟩ _ ⟨j⟩; exact (hpull i j).hasPullback⟩
  have hcompat_iff (x : ∀ i, presentationLimit (P := P) Y.pair.plus (U i)) :
      Presieve.Arrows.PullbackCompatible globalSections
        (fun i ↦ (Y.rationalLocalizationHom (T i) (s i) (hT i)).op)
        (fun i ↦ ePiece i (x i)) ↔
      ∀ i j, (presentationLimitMap (P := P) (inf_le_left : U i ⊓ U j ≤ U i)).hom.val (x i) =
        (presentationLimitMap (P := P) (inf_le_right : U i ⊓ U j ≤ U j)).hom.val (x j) :=
    forall₂_congr fun i j ↦
      @rationalLocalization_compatible_iff Y (T i) (T j) (T' i j) (s i) (s j) (s' i j)
        (hT i) (hT j) (hT' i j) (hUij i j).symm (hinter i j) (hpull i j).hasPullback
        (hpull i j) (x i) (x j)
  rw [rationalCoverPresieve_eq_ofArrows, Presieve.isSheafFor_arrows_iff_pullbacks,
    isSheafFor_ofArrows_iff_existsUnique_presentationLimitMap P (fun i ↦ (le_top : U i ≤ ⊤))]
  refine ⟨fun hO x hx ↦ ?_, fun hLim y hy ↦ ?_⟩
  · obtain ⟨b, hb, hbu⟩ := hO (fun i ↦ ePiece i (x i)) ((hcompat_iff x).mpr hx)
    refine ⟨eTop b, fun i ↦ (ePiece i).injective
        ((presentationLimitRationalEquiv_top Y (T i) (s i) (hT i) b).trans (hb i)),
      fun a ha ↦ ?_⟩
    rw [← eTop.apply_symm_apply a]
    refine congrArg eTop (hbu (eTop.symm a) fun i ↦ ?_)
    rw [globalSections_map_apply, ← presentationLimitRationalEquiv_top Y (T i) (s i) (hT i),
      eTop.apply_symm_apply, ha i]
  · let y' : ∀ i, (Y.rationalLocalization (T i) (s i) (hT i)).ring := y
    have hy_eq : (fun i ↦ (ePiece i ((ePiece i).symm (y' i)) :
        globalSections.obj (op (op (Y.rationalLocalization (T i) (s i) (hT i)))))) = y :=
      funext fun i ↦ (ePiece i).apply_symm_apply (y' i)
    obtain ⟨a, ha, hau⟩ := hLim (fun i ↦ (ePiece i).symm (y' i))
      ((hcompat_iff (fun i ↦ (ePiece i).symm (y' i))).mp (hy_eq.symm ▸ hy))
    refine ⟨(eTop.symm a : Y.ring), fun i ↦ ?_, fun b hb ↦ ?_⟩
    · rw [globalSections_map_apply, ← presentationLimitRationalEquiv_top Y (T i) (s i) (hT i),
        eTop.apply_symm_apply, ha i, Equiv.apply_symm_apply]
    · let b₀ : Y.ring := b
      have hb₀ : b₀ = eTop.symm a := by
        rw [← eTop.symm_apply_apply b₀]
        refine congrArg eTop.symm (hau (eTop b₀) fun i ↦ (ePiece i).injective ?_)
        rw [presentationLimitRationalEquiv_top Y (T i) (s i) (hT i), Equiv.apply_symm_apply]
        exact (globalSections_map_apply _ b₀).symm.trans (hb i)
      exact hb₀

/-- Topological sheafiness (`IsSheafyForEveryPresentation`) passes along any rational localization
`φ : X ⟶ Y` in `CAff`, without any Tate hypothesis. -/
theorem IsRationalLocalization.isSheafyForEveryPresentation {X Y : CAff.{u}} {φ : X ⟶ Y}
    {T₀ : Finset X.ring} {s₀ : X.ring} (hφ : IsRationalLocalization φ T₀ s₀)
    (hX : IsSheafyForEveryPresentation X.pair.plus) :
    IsSheafyForEveryPresentation Y.pair.plus := by
  let P := X.pairOfDefinition
  let hden := hasDenominatorPower_of_isOpen_span P T₀ s₀ (Localization.Away s₀) hφ.isOpen_span
  let _ := locUniformSpace P T₀ s₀ (Localization.Away s₀) hden
  let _ := isUniformAddGroup_locUniformSpace P T₀ s₀ (Localization.Away s₀) hden
  let _ := isTopologicalRing_locUniformSpace P T₀ s₀ (Localization.Away s₀) hden
  let _ := isHuberRing_completion_locTopology P T₀ s₀ (Localization.Away s₀) hden
  let Bplus := completedPlusSubring P X.pair.plus T₀ s₀ (Localization.Away s₀) hden
  have hBplus : IsSheafyForEveryPresentation Bplus := by
    rw [isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf
      (completionLocalization P T₀ s₀ (Localization.Away s₀) hden)]
    exact ⟨isRingOfIntegralElements_completedPlusSubring P X.pair.plus
        (fun j _ ↦ X.ringOfDefinition_le_plus j.property)
        X.pair.isRingOfIntegralElements.isPowerBounded_of_mem T₀ s₀ (Localization.Away s₀) hden,
      isSheaf_presentationLimitPresheaf_completionLocalization P X.pair.plus
        X.pair.isRingOfIntegralElements.isPowerBounded_of_mem X.ringOfDefinition_le_plus
        T₀ s₀ (Localization.Away s₀) hden hφ.isOpen_span
        (hX.isSheaf P X.ringOfDefinition_le_plus)⟩
  let eIso := hφ.isoCanonical
  let eCan : (X.rationalLocalization T₀ s₀ hφ.isOpen_span).ring ≃+* Y.ring :=
    (ringPresheaf.mapIso eIso.op.op).commRingCatIsoToRingEquiv
  let eRing : UniformSpace.Completion (Localization.Away s₀) ≃+* Y.ring :=
    (rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span).symm.trans eCan
  have heRing_cont : Continuous eRing :=
    eIso.hom.continuous_toRingHom.comp
      (continuous_rationalLocalizationRingEquiv_symm X T₀ s₀ hφ.isOpen_span)
  have heRing_symm_cont : Continuous eRing.symm :=
    (continuous_rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span).comp
      eIso.inv.continuous_toRingHom
  have hplus : Bplus.map (eRing : _ →+* Y.ring) = Y.pair.plus := by
    ext y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, ha, rfl⟩
      refine eIso.hom.map_mem_plus _ ((mem_rationalLocalization_plus_iff X T₀ s₀ _ _).mpr ?_)
      change (rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span)
        ((rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span).symm a) ∈ _
      rw [RingEquiv.apply_symm_apply]
      exact ha
    · refine ⟨(rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span) (eIso.inv.toRingHom y),
        (mem_rationalLocalization_plus_iff X T₀ s₀ _ _).mp (eIso.inv.map_mem_plus y hy), ?_⟩
      change eIso.hom.toRingHom
        ((rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span).symm
          ((rationalLocalizationRingEquiv X T₀ s₀ hφ.isOpen_span) (eIso.inv.toRingHom y))) = y
      rw [RingEquiv.symm_apply_apply]
      exact eCan.right_inv y
  exact (isSheafyForEveryPresentation_iff_of_ringEquiv eRing heRing_cont heRing_symm_cont
    hplus).mp hBplus

/-- Every topologically sheafy complete Hausdorff Huber pair `X : CAff.{u}` is rational-sheafy
(without any Tate hypothesis). -/
theorem IsRationalSheafy.of_isSheafyForEveryPresentation {X : CAff.{u}}
    (hX : IsSheafyForEveryPresentation X.pair.plus) : X.IsRationalSheafy := by
  rw [isRationalSheafy_iff]
  intro Y φ T₀ s₀ hφ R hR
  rw [mem_rationalCoverage_iff] at hR
  obtain ⟨ι, _, T, s, hcov, rfl⟩ := hR
  have hsheaf_set := Presheaf.isSheaf_comp_of_isSheaf _ _
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat)
    ((hφ.isSheafyForEveryPresentation hX).isSheaf Y.pairOfDefinition Y.ringOfDefinition_le_plus)
  rw [isSheafFor_globalSections_rationalCoverPresieve_iff, Presieve.isSheafFor_iff_generate]
  refine hsheaf_set.isSheafFor _ ?_
  refine sieve_ofArrows_mem_grothendieckTopology (fun i ↦ le_top) fun x _ ↦ ?_
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov.iUnion_eq_univ ▸ Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨i, mem_spaBasicOpen.mpr hxi⟩

/-- **Equivalence of site-theoretic and topological sheafiness for complete Tate Huber pairs.**
For a complete Hausdorff Tate Huber pair `X : CAff.{u}`, `X.IsRationalSheafy` holds if and only if
`X.pair.plus` satisfies `IsSheafyForEveryPresentation` (the structure presheaf of `Spa(X)` is a
sheaf of complete separated topological rings). -/
theorem isRationalSheafy_iff_isSheafyForEveryPresentation (X : CAff.{u}) [IsTateRing X.ring] :
    X.IsRationalSheafy ↔ IsSheafyForEveryPresentation X.pair.plus := by
  refine ⟨fun hrat ↦ ?_, IsRationalSheafy.of_isSheafyForEveryPresentation⟩
  rw [isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf X.pairOfDefinition]
  refine ⟨X.pair.isRingOfIntegralElements, ?_⟩
  let P := X.pairOfDefinition
  have hAplus := X.pair.isRingOfIntegralElements.isPowerBounded_of_mem
  refine isSheaf_presentationLimitPresheaf_of_isSheafFor_finite_rationalOpens P hAplus
    fun {W} {κ} hfin {V} hW hV hcov ↦ ?_
  obtain ⟨T₀, s₀, hT₀, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hW
  let hden₀ := hasDenominatorPower_of_isOpen_span P T₀ s₀ (Localization.Away s₀) hT₀
  let _ := locUniformSpace P T₀ s₀ (Localization.Away s₀) hden₀
  have _ := isUniformAddGroup_locUniformSpace P T₀ s₀ (Localization.Away s₀) hden₀
  have _ := isTopologicalRing_locUniformSpace P T₀ s₀ (Localization.Away s₀) hden₀
  have _ := isHuberRing_completion_locTopology P T₀ s₀ (Localization.Away s₀) hden₀
  let Y₀ := X.rationalLocalization T₀ s₀ hT₀
  let Q₀ := completionLocalization P T₀ s₀ (Localization.Away s₀) hden₀
  let Bplus := completedPlusSubring P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀
  let Y : CAff.{u} := CAff.of (P.rationalLocalizationPair X.pair X.ringOfDefinition_le_plus T₀ s₀
    (Localization.Away s₀) hden₀)
  have hY_plus : Y.pair.plus = Bplus :=
    P.rationalLocalizationPair_plus X.pair X.ringOfDefinition_le_plus T₀ s₀
      (Localization.Away s₀) hden₀
  let eIso : Y₀ ≅ Y := isoMk (rationalLocalizationRingEquiv X T₀ s₀ hT₀)
    (continuous_rationalLocalizationRingEquiv X T₀ s₀ hT₀)
    (continuous_rationalLocalizationRingEquiv_symm X T₀ s₀ hT₀)
    fun a ↦ (mem_rationalLocalization_plus_iff X T₀ s₀ hT₀ a).trans (by rw [hY_plus])
  have hVW (k : κ) : V k ≤ spaBasicOpen X.pair.plus T₀ s₀ := (le_iSup V k).trans_eq hcov
  -- Transport `IsSheafFor` along `j : Spa(Y) → Spa(X)` via Wedhorn Remark 8.4.
  rw [isSheafFor_ofArrows_iff_locOpensComap P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀
    hAplus hT₀ hW le_rfl hV hVW]
  choose T' s' hT' hU'_eq using fun k ↦ mem_spaRationalOpens_iff_exists_spaBasicOpen.mp <|
    locOpensComap_mem_spaRationalOpens P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀ (hV k)
  have htop_loc : locOpensComap P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀
      (spaBasicOpen X.pair.plus T₀ s₀) = ⊤ :=
    le_antisymm le_top fun w _ ↦ (mem_locOpensComap P X.pair.plus T₀ s₀ _ hden₀ _ w).mpr <|
      mem_spaBasicOpen.mpr (spaComapLoc_mem_rationalSubset P X.pair.plus T₀ s₀ _ hden₀ w)
  have hcovY : IsRationalCovering Y T' s' :=
    { isOpen_span := fun k ↦ hT' k
      iUnion_eq_univ := Set.eq_univ_of_forall fun w ↦ by
        let w' : ↥(ValuationSpectrum.spa Bplus) := ⟨w.val, hY_plus ▸ w.property⟩
        obtain ⟨k, hwk⟩ := Opens.mem_iSup.mp <| hcov ▸ mem_spaBasicOpen.mpr
          (spaComapLoc_mem_rationalSubset P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀ w')
        have hw' : w'.val ∈ rationalSubset Bplus (T' k) (s' k) :=
          mem_spaBasicOpen.mp <| hU'_eq k ▸
            (mem_locOpensComap P X.pair.plus T₀ s₀ (Localization.Away s₀) hden₀ (V k) w').mpr hwk
        exact Set.mem_iUnion.mpr ⟨k, show w.val ∈ rationalSubset Y.pair.plus (T' k) (s' k) from
          congrArg (rationalSubset · (T' k) (s' k)) hY_plus ▸ hw'⟩ }
  -- Apply `hrat` to the rational localization `X ⟶ Y` and the rational cover `(T', s')`.
  have hLim_Q₀ := (isSheafFor_presentationLimitPresheaf_comp_iff_of_pairOfDefinition
    Y.pairOfDefinition Q₀ Y.pair.plus
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget _root_.TopCommRingCat) _).mp <|
    (isSheafFor_globalSections_rationalCoverPresieve_iff Y T' s' hcovY.isOpen_span).mp <|
      hrat.isSheafFor
        ((isRationalLocalization_rationalLocalizationHom X T₀ s₀ hT₀).comp_iso eIso)
        (rationalCoverPresieve_mem_rationalCoverage Y T' s' hcovY)
  rw [hY_plus] at hLim_Q₀
  exact (isSheafFor_ofArrows_congr _ htop_loc (funext hU'_eq) _ _).mpr hLim_Q₀

end TauCeti.CAff

end
