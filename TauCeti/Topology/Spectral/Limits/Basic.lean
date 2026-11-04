/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.PatchCriterion
public import TauCeti.Topology.Spectral.ProConstructible
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.WithTopology

/-!
# Limits of spectral spaces

Products of spectral spaces are spectral. Equalizers of spectral maps into a T₀ prespectral
space are pro-constructible, so the compatible locus of a diagram of spectral spaces with
spectral transition maps is spectral as well. Its coordinate projections are spectral.
These results apply to arbitrary small diagrams, including cofiltered inverse systems and the
empty diagram.

The product proof uses `TauCeti.spectralSpace_of_isClopen_generateFrom`: finite cylinders of
compact opens are clopen for the compact product of the constructible topologies. Compatibility
is expressed by agreement on compact opens, avoiding any Hausdorff assumption on the original
spaces. The limit is Mathlib's `TopCat.limitCone`, with its ordinary subspace topology.

## References

* P. Scholze, *Étale cohomology of diamonds*, §2, Lemma 2.11 (spectral inverse limits).
-/

public section

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TauCeti

/-- An arbitrary product of spectral spaces, with its product topology, is spectral. -/
instance spectralSpace_pi {ι : Type*} {X : ι → Type*} [t : ∀ i, TopologicalSpace (X i)]
    [∀ i, SpectralSpace (X i)] : SpectralSpace (∀ i, X i) := by
  have hb := isTopologicalBasis_pi (fun i ↦ PrespectralSpace.isTopologicalBasis (X := X i))
  have hgen := hb.eq_generateFrom
  have hT0 : T0Space (∀ i, X i) := inferInstance
  let t' : TopologicalSpace (∀ i, X i) :=
    @Pi.topologicalSpace ι X (fun i ↦ constructibleTopology (X i))
  have hc : @CompactSpace (∀ i, X i) t' := by
    have hcomp (i) : @CompactSpace (X i) (constructibleTopology (X i)) :=
      @Function.Surjective.compactSpace (WithConstructibleTopology (X i)) (X i) _
        (constructibleTopology (X i)) WithTopology.ofTopology
        (WithTopology.continuous_ofTopology _) inferInstance
        (WithTopology.ofTopology_surjective _)
    exact @Pi.compactSpace ι X (fun i ↦ constructibleTopology (X i)) hcomp
  refine @spectralSpace_of_isClopen_generateFrom _ _ t' (@Pi.topologicalSpace ι X t) hgen hc ?_ hT0
  rintro U ⟨V, s, hV, rfl⟩
  rw [Set.pi_def]
  exact @isClopen_biInter_finset _ t' _ s (fun i ↦ (fun x ↦ x i) ⁻¹' V i) fun i hi ↦
    @IsClopen.preimage _ _ t' (constructibleTopology (X i)) _
      ((hV i hi).2.isClopen_constructibleTopology_of_isOpen (hV i hi).1)
      (fun x ↦ x i) (@continuous_apply ι X (fun i ↦ constructibleTopology (X i)) i)

end TauCeti

namespace TopCat

universe v u w

variable {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{max v u})
  [∀ j, SpectralSpace (F.obj j)]
  (hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f))

include hF

/-- The compatible locus defining the limit of a diagram of spectral spaces with spectral
transition maps is pro-constructible in the product. -/
theorem isProConstructible_limitCone :
    TauCeti.IsProConstructible
      {x : ∀ j, F.obj j | ∀ ⦃i j⦄ (f : i ⟶ j), F.map f (x i) = x j} := by
  have heq : {x : ∀ j, F.obj j | ∀ ⦃i j⦄ (f : i ⟶ j), F.map f (x i) = x j} =
      ⋂ i, ⋂ j, ⋂ f : i ⟶ j, {x | F.map f (x i) = x j} := by
    ext x
    simp
  rw [heq]
  refine TauCeti.IsProConstructible.iInter fun i ↦
    TauCeti.IsProConstructible.iInter fun j ↦ TauCeti.IsProConstructible.iInter fun f ↦ ?_
  have hi : IsSpectralMap (fun x : ∀ j, F.obj j ↦ x i) :=
    TauCeti.isSpectralMap_eval i fun _ _ ↦ isCompact_univ
  have hj : IsSpectralMap (fun x : ∀ j, F.obj j ↦ x j) :=
    TauCeti.isSpectralMap_eval j fun _ _ ↦ isCompact_univ
  exact ((hF f).comp hi).isProConstructible_eq hj

/-- The limit of any small diagram of spectral spaces and spectral maps is spectral, on
Mathlib's compatible-locus carrier with its subspace topology. In particular this applies to
cofiltered inverse limits. -/
theorem spectralSpace_limitCone : SpectralSpace (limitCone F).pt :=
  (isProConstructible_limitCone F hF).spectralSpace

/-- Every coordinate projection of the compatible-locus limit of spectral spaces and spectral
maps is spectral. -/
theorem isSpectralMap_limitCone_π (j : J) : IsSpectralMap ((limitCone F).π.app j) := by
  have hp := (TauCeti.isSpectralMap_eval j fun _ _ ↦ isCompact_univ).comp
    (isProConstructible_limitCone F hF).isSpectralMap_subtypeVal
  exact hp

/-- Spectrality of a limit is independent of the chosen limiting cone. -/
theorem spectralSpace_of_isLimit (c : Cone F) (hc : IsLimit c) : SpectralSpace c.pt := by
  have := spectralSpace_limitCone F hF
  let e := homeoOfIso (hc.conePointUniqueUpToIso (limitConeIsLimit F))
  have : CompactSpace c.pt := e.symm.compactSpace
  exact e.isOpenEmbedding.spectralSpace

/-- The projections of any limiting cone of spectral spaces and spectral maps are spectral. -/
theorem isSpectralMap_of_isLimit_π (c : Cone F) (hc : IsLimit c) (j : J) :
    IsSpectralMap (c.π.app j) := by
  let e := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have he : e.hom ≫ (limitCone F).π.app j = c.π.app j :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
  rw [← he]
  exact (isSpectralMap_limitCone_π F hF j).comp (homeoOfIso e).isProperMap.isSpectralMap

end TopCat
