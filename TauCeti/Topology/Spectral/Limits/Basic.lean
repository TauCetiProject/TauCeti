/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallySpectral
public import TauCeti.Topology.Spectral.PatchCriterion
public import TauCeti.Topology.Spectral.ProConstructible
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.WithTopology

/-!
# Limits of spectral spaces

Arbitrary and binary products of spectral spaces are spectral, binary products of locally spectral
spaces are locally spectral, and each projection of a binary product is locally spectral when the
complementary factor is locally spectral. Equalizers of spectral maps
into a T₀ prespectral space are pro-constructible, so the compatible locus of a diagram of spectral
spaces with spectral transition maps is spectral as well. Its coordinate projections are spectral.
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

/-- A binary product of spectral spaces is spectral. -/
instance spectralSpace_prod {X : Type*} {Y : Type*} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) := by
  have hb := (PrespectralSpace.isTopologicalBasis (X := X)).prod
    (PrespectralSpace.isTopologicalBasis (X := Y))
  have hgen := hb.eq_generateFrom
  have hT0 : T0Space (X × Y) := inferInstance
  let t' : TopologicalSpace (X × Y) :=
    @instTopologicalSpaceProd X Y (constructibleTopology X) (constructibleTopology Y)
  have hc : @CompactSpace (X × Y) t' := by
    let _ : TopologicalSpace X := constructibleTopology X
    let _ : TopologicalSpace Y := constructibleTopology Y
    exact ((WithTopology.ofTopology_surjective _).prodMap
      (WithTopology.ofTopology_surjective _)).compactSpace
      ((WithTopology.continuous_ofTopology _).prodMap (WithTopology.continuous_ofTopology _))
  refine @spectralSpace_of_isClopen_generateFrom _ _ t' (@instTopologicalSpaceProd X Y tX tY)
    hgen hc ?_ hT0
  rintro _ ⟨U, ⟨hUo, hUc⟩, V, ⟨hVo, hVc⟩, rfl⟩
  exact @IsClopen.prod X Y (constructibleTopology X) (constructibleTopology Y) U V
    (hUc.isClopen_constructibleTopology_of_isOpen hUo)
    (hVc.isClopen_constructibleTopology_of_isOpen hVo)

/-- A binary product of locally spectral spaces is locally spectral. -/
theorem IsLocallySpectralSpace.prod {X : Type*} {Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hX : IsLocallySpectralSpace X) (hY : IsLocallySpectralSpace Y) :
    IsLocallySpectralSpace (X × Y) :=
  isLocallySpectralSpace_iff.mpr fun ⟨x, y⟩ ↦ by
    obtain ⟨U, hUo, hxU, hUs⟩ := isLocallySpectralSpace_iff.mp hX x
    obtain ⟨V, hVo, hyV, hVs⟩ := isLocallySpectralSpace_iff.mp hY y
    have := hUs
    have := hVs
    exact ⟨U ×ˢ V, hUo.prod hVo, ⟨hxU, hyV⟩, (Homeomorph.Set.prod U V).symm.spectralSpace⟩

/-- The first projection `X × Y → X` is locally spectral whenever the second factor `Y` is locally
spectral. -/
theorem IsLocallySpectralSpace.isLocallySpectralMap_fst {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (hY : IsLocallySpectralSpace Y) :
    IsLocallySpectralMap (Prod.fst : X × Y → X) := by
  refine .of_isSpectralMap_restrict continuous_fst fun W U hWU hWo hUo hWs hUs ↦ ?_
  let _ : SpectralSpace W := hWs
  let _ : SpectralSpace U := hUs
  have hfstU : IsLocallySpectralMap (Prod.fst : U × Y → U) := by
    refine IsLocallySpectralMap.of_forall_exists fun ⟨u, y⟩ ↦ ?_
    obtain ⟨U', hU'o, huU', hU's⟩ :=
      isLocallySpectralSpace_iff.mp SpectralSpace.isLocallySpectralSpace u
    obtain ⟨V, hVo, hyV, hVs⟩ := isLocallySpectralSpace_iff.mp hY y
    have := hU's
    have := hVs
    have hU'V : MapsTo (Prod.fst : U × Y → U) (U' ×ˢ V) U' := fun _ h ↦ h.1
    have hU'Vs : SpectralSpace ↥(U' ×ˢ V) := (Homeomorph.Set.prod U' V).symm.spectralSpace
    refine ⟨U' ×ˢ V, U', hU'V, hU'o.prod hVo, hU'o, ⟨huU', hyV⟩, hU'Vs.toQuasiSeparatedSpace, ?_⟩
    have heq : hU'V.restrict Prod.fst (U' ×ˢ V) U' = Prod.fst ∘ Homeomorph.Set.prod U' V := by
      funext _
      rfl
    rw [heq]
    exact isProperMap_fst_of_compactSpace.isSpectralMap.comp
      (Homeomorph.Set.prod U' V).isProperMap.isSpectralMap
  let ι : W → U × Y := fun w ↦ (⟨w.1.1, hWU w.2⟩, w.1.2)
  have hι : IsOpenEmbedding ι := by
    refine IsOpenEmbedding.of_comp ι (hUo.isOpenEmbedding_subtypeVal.prodMap .id) ?_
    have heq : (Prod.map (Subtype.val : U → X) id) ∘ ι = (Subtype.val : W → X × Y) := by
      funext _
      rfl
    rw [heq]
    exact hWo.isOpenEmbedding_subtypeVal
  have hls : IsLocallySpectralMap (Prod.fst ∘ ι) :=
    IsLocallySpectralMap.comp (SpectralSpace.isLocallySpectralSpace.prod hY)
      hfstU hι.isLocallySpectralMap
  have heq : hWU.restrict Prod.fst W U = Prod.fst ∘ ι := by
    funext _
    rfl
  rw [heq]
  exact hls.isSpectralMap

/-- The second projection `X × Y → Y` is locally spectral whenever the first factor `X` is locally
spectral. -/
theorem IsLocallySpectralSpace.isLocallySpectralMap_snd {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : IsLocallySpectralSpace X) :
    IsLocallySpectralMap (Prod.snd : X × Y → Y) := by
  refine .of_isSpectralMap_restrict continuous_snd fun W V hWV hWo hVo hWs hVs ↦ ?_
  let _ : SpectralSpace W := hWs
  let _ : SpectralSpace V := hVs
  let e : W ≃ₜ (Prod.swap ⁻¹' W) := (Homeomorph.prodComm X Y).subtype fun _ ↦ Iff.rfl
  have _ : SpectralSpace (Prod.swap ⁻¹' W) := e.spectralSpace
  have hW'V : MapsTo (Prod.fst : Y × X → Y) (Prod.swap ⁻¹' W) V := fun _ h ↦ hWV h
  have heq : hWV.restrict Prod.snd W V = (hW'V.restrict Prod.fst (Prod.swap ⁻¹' W) V) ∘ e := by
    funext _
    rfl
  rw [heq]
  exact (hX.isLocallySpectralMap_fst.isSpectralMap_restrict hW'V
    (hWo.preimage continuous_swap) hVo).comp e.isProperMap.isSpectralMap

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
