/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Restrict
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Topology

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.GlobalSections
import TauCeti.RingTheory.Huber.LocalizationTopology.StronglyNoetherian

/-!
# The topology on sections of a Laurent cover

For a strongly noetherian Tate ring, restriction from a rational open to its two-piece Laurent
cover is a closed embedding. Thus the topology on sections is the equalizer topology inherited
from the product of the rings of sections on the two pieces. This supplies the topological part
of Laurent gluing, in addition to the algebraic exactness of the restriction maps.

For the whole spectrum of a complete Hausdorff ring, the assertion follows from the closed
embedding into the completed rational localizations and the topological-ring isomorphisms
identifying these localizations with sections. Rational localization then gives the assertion
on any rational open, without a completeness or separatedness assumption on the original ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.4, Lemma 8.33,
  Lemma 8.34(i), and Remark 8.20.
-/

public section

open CategoryTheory TopologicalSpace Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

attribute [local instance] Classical.decEq

section Top

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]
  (P : PairOfDefinition A) {Aplus : Subring A}

/-- Restriction from the whole spectrum to a two-piece Laurent cover is a closed embedding for
a complete Hausdorff strongly noetherian Tate ring. -/
private theorem isClosedEmbedding_presentationLimitMap_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A) :
    IsClosedEmbedding fun x : presentationLimit (P := P) Aplus ⊤ ↦
      ((presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f true ≤ ⊤)).hom.1 x,
        (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f false ≤ ⊤)).hom.1 x) := by
  have hopen (b : Bool) : IsOpen
      (Ideal.span ((cond b {f, 1} {1} : Finset A) : Set A) : Set A) := by
    have hone (b : Bool) : (1 : A) ∈ (cond b {f, 1} {1} : Finset A) := by
      cases b <;> simp
    exact (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span (hone b)) ▸ isOpen_univ
  let p (b : Bool) : Presentation P :=
    ⟨cond b {f, 1} {1}, cond b 1 f,
      hasDenominatorPower_of_isOpen_span P _ _ _ (hopen b)⟩
  let _ := locUniformSpace P {f, 1} 1 (Localization.Away (1 : A)) (p true).hasDenominatorPower
  let _ := locUniformSpace P {1} f (Localization.Away f) (p false).hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 (Localization.Away (1 : A))
    (p true).hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 (Localization.Away (1 : A))
    (p true).hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P {1} f (Localization.Away f)
    (p false).hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P {1} f (Localization.Away f)
    (p false).hasDenominatorPower
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  -- Conjugate the augmentation by the canonical isomorphisms on the source and both targets.
  let d : presentationLimit (P := P) Aplus ⊤ ≃ₜ A :=
    (TopCat.homeoOfIso (F.mapIso (presentationLimitTopIso (P := P) Aplus hAplus))).trans
    (TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso
      (eqToIso (CompleteSeparatedTopCommRingCat.of_obj A))))
  let e₁ : presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f true) ≃ₜ
      UniformSpace.Completion (Localization.Away (1 : A)) :=
    (TopCat.homeoOfIso (F.mapIso
      (presentationLimitRationalIso Aplus hAplus (p true) (hopen true)))).trans
      (TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso
        (eqToIso (completionLocObj_obj P {f, 1} 1 (Localization.Away (1 : A))
          (p true).hasDenominatorPower))))
  let e₂ : presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f false) ≃ₜ
      UniformSpace.Completion (Localization.Away f) :=
    (TopCat.homeoOfIso (F.mapIso
      (presentationLimitRationalIso Aplus hAplus (p false) (hopen false)))).trans
      (TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso
        (eqToIso (completionLocObj_obj P {1} f (Localization.Away f)
          (p false).hasDenominatorPower))))
  let e := e₁.prodCongr e₂
  have hemb := (isClosedEmbedding_laurentCover P f (Localization.Away (1 : A))
    (Localization.Away f) (p false).hasDenominatorPower).comp d.isClosedEmbedding
  apply e.isClosedEmbedding.of_comp_iff.mp
  suffices heq : e ∘ (fun x : presentationLimit (P := P) Aplus ⊤ ↦
      ((presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f true ≤ ⊤)).hom.1 x,
        (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f false ≤ ⊤)).hom.1 x)) =
      (RingHom.prod (toCompletionLoc P {f, 1} 1 (Localization.Away (1 : A))
        (p true).hasDenominatorPower) (toCompletionLoc P {1} f (Localization.Away f)
        (p false).hasDenominatorPower)) ∘ d by
    rw [heq]
    exact hemb
  funext x
  have := isIso_toPresentationLimit_top (P := P) Aplus hAplus
  have hsurj : Function.Surjective (toPresentationLimit (P := P) Aplus ⊤).hom.1 :=
    Function.RightInverse.surjective
      (asIso (toPresentationLimit (P := P) Aplus ⊤)).inv_hom_id_apply
  obtain ⟨c, rfl⟩ := hsurj x
  -- Evaluate the canonical projection identity, rather than unfolding the presentation limit.
  have key (b : Bool) : toPresentationLimit Aplus ⊤ ≫ presentationLimitMap le_top ≫
      (presentationLimitRationalIso Aplus hAplus (p b) (hopen b)).hom =
        (p b).toCompletionLocObjHom := by simp
  have hk (b : Bool) := congrArg (fun g ↦
    (eqToHom (completionLocObj_obj P (p b).num (p b).den _ (p b).hasDenominatorPower)).1
      (g.hom.1 c)) (key b)
  -- These evaluation identities remove only the categorical homeomorphism wrappers.
  have hd_apply (z : presentationLimit (P := P) Aplus ⊤) : d z =
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1
        ((presentationLimitTopIso (P := P) Aplus hAplus).hom.hom.1 z) := (rfl)
  have he₁_apply (z : presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f true)) :
      e₁ z = (eqToHom (completionLocObj_obj P {f, 1} 1 (Localization.Away (1 : A))
        (p true).hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus (p true) (hopen true)).hom.hom.1 z) := (rfl)
  have he₂_apply (z : presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f false)) :
      e₂ z = (eqToHom (completionLocObj_obj P {1} f (Localization.Away f)
        (p false).hasDenominatorPower)).1
          ((presentationLimitRationalIso Aplus hAplus (p false) (hopen false)).hom.hom.1 z) := (rfl)
  have hd : d ((toPresentationLimit (P := P) Aplus ⊤).hom.1 c) =
      (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 c := by
    rw [hd_apply]
    have h := (presentationLimitTopIso (P := P) Aplus hAplus).inv_hom_id_apply c
    rw [presentationLimitTopIso_inv] at h
    exact congrArg (eqToHom (CompleteSeparatedTopCommRingCat.of_obj A)).1 h
  apply Prod.ext
  all_goals
    simp only [Function.comp_apply, RingHom.prod_apply, e, Homeomorph.coe_prodCongr,
      Prod.map_apply]
    rw [hd]
  · rw [he₁_apply]
    refine (hk true).trans ?_
    rw [Presentation.toCompletionLocObjHom_hom]
    exact (eqToIso (completionLocObj_obj P {f, 1} 1 (Localization.Away (1 : A))
      (p true).hasDenominatorPower)).inv_hom_id_apply _
  · rw [he₂_apply]
    refine (hk false).trans ?_
    rw [Presentation.toCompletionLocObjHom_hom]
    exact (eqToIso (completionLocObj_obj P {1} f (Localization.Away f)
      (p false).hasDenominatorPower)).inv_hom_id_apply _

end Top

section Rational

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- Restriction from any rational open to its two-piece Laurent cover is a closed embedding.
The original strongly noetherian Tate ring need not be complete or Hausdorff. Together with
Laurent gluing, this identifies sections with the topological equalizer of the overlap maps. -/
theorem isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {W : Opens ↥(spa Aplus)}
    (hW : W ∈ spaRationalOpens Aplus) (f : A) :
    IsClosedEmbedding fun x : presentationLimit (P := P) Aplus W ↦
      ((presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f true ≤ W)).hom.1 x,
        (presentationLimitMap (P := P)
          (inf_le_left : W ⊓ laurentCoverOpen Aplus f false ≤ W)).hom.1 x) := by
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hW
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := isStronglyNoetherian_completion P T s _ hden
    (eq_top_mono (Ideal.span_mono (Set.subset_insert _ _)) (IsTateRing.eq_top_of_isOpen hT))
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  let Q := completionLocalization P T s (Localization.Away s) hden
  let Bplus := completedPlusSubring P Aplus T s (Localization.Away s) hden
  let g := toCompletionLoc P T s (Localization.Away s) hden f
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  have hrat := spaBasicOpen_mem_spaRationalOpens (Aplus := Aplus) (s := s) hT
  have hU (b : Bool) := inf_mem_spaRationalOpens hrat
    (laurentCoverOpen_mem_spaRationalOpens Aplus f b)
  let d : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃ₜ
      presentationLimit (P := Q) Bplus ⊤ := TopCat.homeoOfIso (F.mapIso
    (presentationLimitLocIso P Aplus T s _ hden hAplus hT _ hrat le_rfl ≪≫
      eqToIso (congrArg (presentationLimit (P := Q) Bplus)
        (locOpensComap_spaBasicOpen_self P Aplus T s _ hden))))
  let e (b : Bool) :
      presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b) ≃ₜ
        presentationLimit (P := Q) Bplus (laurentCoverOpen Bplus g b) :=
    TopCat.homeoOfIso (F.mapIso
      (presentationLimitLocIso P Aplus T s _ hden hAplus hT _ (hU b) inf_le_left ≪≫
        eqToIso (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f b))))
  have hemb := (isClosedEmbedding_presentationLimitMap_laurentCoverOpen Q
    (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) g).comp
      d.isClosedEmbedding
  apply (e true |>.prodCongr (e false)).isClosedEmbedding.of_comp_iff.mp
  suffices heq : (e true |>.prodCongr (e false)) ∘
      (fun x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ↦
        ((presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
          laurentCoverOpen Aplus f true ≤ _)).hom.1 x,
          (presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
            laurentCoverOpen Aplus f false ≤ _)).hom.1 x)) =
      (fun x : presentationLimit (P := Q) Bplus ⊤ ↦
        ((presentationLimitMap (P := Q) (le_top : laurentCoverOpen Bplus g true ≤ ⊤)).hom.1 x,
          (presentationLimitMap (P := Q) (le_top : laurentCoverOpen Bplus g false ≤ ⊤)).hom.1 x)) ∘
        d by
    rw [heq]
    exact hemb
  -- Naturality of Remark 8.4, followed by transport of the pullback opens to Laurent pieces.
  have hn (b : Bool) := presentationLimitMap_comp_presentationLimitLocIso_hom
    P Aplus T s _ hden hAplus hT hrat (hU b) le_rfl
    (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)
  have ht (b : Bool) :
      presentationLimitMap (P := Q)
          (locOpensComap_mono P Aplus T s _ hden
            (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)) ≫
        eqToHom (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f b)) =
      eqToHom (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_spaBasicOpen_self P Aplus T s _ hden)) ≫
        presentationLimitMap (P := Q) (le_top : laurentCoverOpen Bplus g b ≤ ⊤) := by
    rw [eqToHom_presentationLimit
      (locOpensComap_inf_laurentCoverOpen P Aplus T s _ hden f b) _,
      eqToHom_presentationLimit (locOpensComap_spaBasicOpen_self P Aplus T s _ hden) _]
    simp only [presentationLimitMap_comp]
  funext x
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (((reassoc_of% hn true) _).trans (by rw [ht true])) x
  · exact ConcreteCategory.congr_hom (((reassoc_of% hn false) _).trans (by rw [ht false])) x

end Rational

end TauCeti.ValuationSpectrum
