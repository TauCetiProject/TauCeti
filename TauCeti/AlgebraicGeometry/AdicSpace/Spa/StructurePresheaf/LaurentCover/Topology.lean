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

Restriction from a rational open to its two-piece Laurent cover is transported along rational
localization whenever the corresponding restriction on the completed coordinate ring is a
closed embedding. For a strongly noetherian Tate ring this hypothesis always holds. Thus the
topology on sections is the equalizer topology inherited from the product of the rings of
sections on the two pieces. This supplies the topological part of Laurent gluing, in addition to
the algebraic exactness of the restriction maps.

For the whole spectrum of a complete Hausdorff ring, the assertion follows from the closed
embedding into the completed rational localizations and the topological-ring isomorphisms
identifying these localizations with sections. Rational localization then gives the assertion
on any rational open, without a completeness or separatedness assumption on the original ring.

## Main results

* `isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen_of_locOpensComap` transports a
  closed embedding from a completed rational localization back to the original rational open.
* `isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen` proves the resulting statement
  for strongly noetherian Tate rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.4, Lemma 8.33,
  Lemma 8.34(i), and Remark 8.20.
-/

public section

open CategoryTheory TopologicalSpace Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

attribute [local instance] Classical.decEq

section Transport

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-- **Topological Laurent restriction transported along rational localization.** If restriction
to the two Laurent pieces is a closed embedding on the completed coordinate ring `A⟨T/s⟩`,
then restriction from `R(T/s)` to its two Laurent pieces is a closed embedding. This is the
topological form of Wedhorn's Remark 8.4. -/
theorem isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen_of_locOpensComap
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A)
    (hemb :
      letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      let Q := completionLocalization P T s S hden
      let Bplus := completedPlusSubring P Aplus T s S hden
      let g := toCompletionLoc P T s S hden f
      IsClosedEmbedding fun x : presentationLimit (P := Q) Bplus ⊤ ↦
        ((presentationLimitMap (P := Q)
            (le_top : laurentCoverOpen Bplus g true ≤ ⊤)).hom.1 x,
          (presentationLimitMap (P := Q)
            (le_top : laurentCoverOpen Bplus g false ≤ ⊤)).hom.1 x)) :
    IsClosedEmbedding fun x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ↦
      ((presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
          laurentCoverOpen Aplus f true ≤ _)).hom.1 x,
        (presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
          laurentCoverOpen Aplus f false ≤ _)).hom.1 x) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ : IsHuberRing A := ⟨⟨P⟩⟩
  let Q := completionLocalization P T s S hden
  let Bplus := completedPlusSubring P Aplus T s S hden
  let g := toCompletionLoc P T s S hden f
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ _root_.TopCommRingCat TopCat
  have hrat := spaBasicOpen_mem_spaRationalOpens (Aplus := Aplus) (s := s) hT
  have hU (b : Bool) := inf_mem_spaRationalOpens hrat
    (laurentCoverOpen_mem_spaRationalOpens Aplus f b)
  -- Rational localization identifies the original rational open with the whole localized
  -- spectrum and each of its Laurent pieces with the corresponding localized Laurent piece.
  let d : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ≃ₜ
      presentationLimit (P := Q) Bplus ⊤ := TopCat.homeoOfIso (F.mapIso
    (presentationLimitLocIso P Aplus T s S hden hAplus hT _ hrat le_rfl ≪≫
      eqToIso (congrArg (presentationLimit (P := Q) Bplus)
        (locOpensComap_spaBasicOpen_self P Aplus T s S hden))))
  let e (b : Bool) :
      presentationLimit (P := P) Aplus
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b) ≃ₜ
        presentationLimit (P := Q) Bplus (laurentCoverOpen Bplus g b) :=
    TopCat.homeoOfIso (F.mapIso
      (presentationLimitLocIso P Aplus T s S hden hAplus hT _ (hU b) inf_le_left ≪≫
        eqToIso (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_inf_laurentCoverOpen P Aplus T s S hden f b))))
  -- Conjugate by these homeomorphisms.  The hypothesis supplies the closed embedding on the
  -- localized side, so only commutativity of the conjugated restriction map remains.
  have hclosed := hemb.comp d.isClosedEmbedding
  apply (e true |>.prodCongr (e false)).isClosedEmbedding.of_comp_iff.mp
  suffices heq : (e true |>.prodCongr (e false)) ∘
      (fun x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) ↦
        ((presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
          laurentCoverOpen Aplus f true ≤ _)).hom.1 x,
          (presentationLimitMap (P := P) (inf_le_left : spaBasicOpen Aplus T s ⊓
            laurentCoverOpen Aplus f false ≤ _)).hom.1 x)) =
      (fun x : presentationLimit (P := Q) Bplus ⊤ ↦
        ((presentationLimitMap (P := Q)
            (le_top : laurentCoverOpen Bplus g true ≤ ⊤)).hom.1 x,
          (presentationLimitMap (P := Q)
            (le_top : laurentCoverOpen Bplus g false ≤ ⊤)).hom.1 x)) ∘ d by
    rw [heq]
    exact hclosed
  -- Naturality of rational localization compares the restriction maps before equality transport.
  have hn (b : Bool) := presentationLimitMap_comp_presentationLimitLocIso_hom
    P Aplus T s S hden hAplus hT hrat (hU b) le_rfl
    (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)
  have ht (b : Bool) :
      presentationLimitMap (P := Q)
          (locOpensComap_mono P Aplus T s S hden
            (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)) ≫
        eqToHom (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_inf_laurentCoverOpen P Aplus T s S hden f b)) =
      eqToHom (congrArg (presentationLimit (P := Q) Bplus)
          (locOpensComap_spaBasicOpen_self P Aplus T s S hden)) ≫
        presentationLimitMap (P := Q) (le_top : laurentCoverOpen Bplus g b ≤ ⊤) := by
    rw [eqToHom_presentationLimit
      (locOpensComap_inf_laurentCoverOpen P Aplus T s S hden f b) _,
      eqToHom_presentationLimit (locOpensComap_spaBasicOpen_self P Aplus T s S hden) _]
    simp only [presentationLimitMap_comp]
  -- Combine naturality with the equality-transport calculation in each Laurent coordinate.
  funext x
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (((reassoc_of% hn true) _).trans (by rw [ht true])) x
  · exact ConcreteCategory.congr_hom (((reassoc_of% hn false) _).trans (by rw [ht false])) x

end Transport

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
  exact isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isClosedEmbedding_toCompletionLoc
    P hAplus f fun hden₂ ↦
      isClosedEmbedding_laurentCover P f (Localization.Away (1 : A))
        (Localization.Away f) hden₂

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
  exact isClosedEmbedding_presentationLimitMap_inf_laurentCoverOpen_of_locOpensComap
    P Aplus T s _ hden hAplus hT f
      (isClosedEmbedding_presentationLimitMap_laurentCoverOpen
        (completionLocalization P T s _ hden)
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden)
        (toCompletionLoc P T s _ hden f))

end Rational

end TauCeti.ValuationSpectrum
