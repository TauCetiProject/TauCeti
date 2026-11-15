/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Spectral.Basic
public import TauCeti.Topology.Spectral.ConstructibleTopology
public import TauCeti.Topology.Spectral.PatchCriterion
import Mathlib.Topology.WithTopology

/-!
# A basis criterion for spectral maps, and transport of spectrality along surjections and embeddings

Utilities for spectral spaces and maps. A continuous map is spectral as soon as the preimage
of every member of some topological **basis** of the target is compact; when the map is also
surjective, the same basis hypothesis transfers prespectrality, quasiseparatedness,
quasi-sobriety, and (once the target is `T0Space`) spectrality from the source to the target. A set
contained in the range of an embedding is spectral exactly when its preimage is.

The basis criterion first. Spectrality asks for compact preimages of all compact open sets; the
reduction to a basis is the observation that a compact open set is a *finite* union of basis
elements — cover it by the basis members it contains and extract a finite subcover — and a finite
union of compact preimages is compact.

Nothing is assumed of the basis members themselves, not even compactness: only their preimages
enter the argument. In the intended applications the basis members are the distinguished
quasi-compact opens of a spectral space (Wedhorn's family `R` for `Spv (A, I)`), whose preimages
are computed by hand, or basic open sets of a quotient topology.

Mathlib's `IsSpectralMap` API provides constructors from identities, compositions and embeddings,
but no criterion that tests spectrality on a basis; this supplies the missing entry point.

## Main results

* `TauCeti.isSpectralMap_of_isTopologicalBasis` : a continuous map whose preimages of basis
  members are compact is a spectral map.
* `TauCeti.spectralSpace_of_isTopologicalBasis_of_surjective` : a continuous surjection onto a
  `T0Space` target admitting a basis with compact preimages transfers spectrality from a compact,
  quasi-sober, quasiseparated prespectral source (built from the component transfers
  `prespectralSpace_of_isTopologicalBasis_of_surjective`,
  `quasiSeparatedSpace_of_isTopologicalBasis_of_surjective`, and
  `quasiSober_of_isTopologicalBasis_of_surjective`).
* `Set.MapsTo.isSpectralMap_restrict_iff`: spectrality of a restriction expressed in terms of
  subsets of the ambient spaces.
* `TauCeti.isSpectralMap_eval`: a coordinate projection is spectral when every other factor
  is quasi-compact.
* `Topology.IsEmbedding.spectralSpace_preimage_iff` : a subset of the range of an embedding is
  spectral if and only if its preimage is — the transport step of any subspace spectrality
  argument.
* `IsOpen.exists_spectralSpace_subset_inter`: compact spectral open neighbourhoods inside a
  spectral open subset.
* `TauCeti.spectralSpace_prop`: the Sierpiński space `Prop` is spectral.
* `Topology.IsOpenEmbedding.isSpectralMap` : an open embedding from a compact space into a
  quasiseparated space is spectral.
* `TauCeti.spectralSpace_univ` : the full subspace of a spectral space is spectral.
* `IsSpectralMap.isConstructible_preimage` : constructible sets pull back along spectral maps
  from quasiseparated spaces to compact spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1 — Lemma 7.5(2) is the intended consumer of the
  basis criterion, and Corollary 7.12 and Theorem 7.35 of the transport lemma.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemma 2.9 — target spectrality
  from a basis with compact preimages.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A spectral map from a quasiseparated space to a compact space pulls constructible sets
back to constructible sets. In particular this applies to maps between spectral spaces. -/
theorem _root_.IsSpectralMap.isConstructible_preimage [QuasiSeparatedSpace X] [CompactSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) {s : Set Y} (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _ hUo hUc ↦
    (hf.isCompact_preimage_of_isOpen hUo hUc.isCompact).isRetrocompact
      (hUo.preimage hf.continuous)

/-- **A basis criterion for spectral maps.** A continuous map is spectral as soon as the preimage
of every member of a topological basis of the target is compact: a compact open set is a finite
union of basis members, and a finite union of compact preimages is compact.

The basis members themselves need not be compact — only their preimages appear in the
hypothesis. -/
theorem isSpectralMap_of_isTopologicalBasis {f : X → Y} {B : Set (Set Y)}
    (hB : IsTopologicalBasis B) (hf : Continuous f)
    (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : IsSpectralMap f := by
  refine ⟨hf, fun s hso hs ↦ ?_⟩
  -- Write `s` as a union of basis members, then extract a finite subcover from compactness.
  obtain ⟨S, hSB, rfl⟩ := hB.open_eq_sUnion hso
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun b : S ↦ (b : Set Y))
    (fun b ↦ hB.isOpen (hSB b.2)) Set.sUnion_eq_iUnion.le
  -- The subcover is an equality: every member of `S` is contained in `⋃₀ S`.
  have heq : ⋃₀ S = ⋃ b ∈ t, (b : Set Y) := by
    refine subset_antisymm ht (Set.iUnion₂_subset fun b _ ↦ ?_)
    exact Set.subset_sUnion_of_mem b.2
  rw [heq, Set.preimage_iUnion₂]
  exact t.isCompact_biUnion fun b _ ↦ hpre b (hSB b.2)

/-- A space admitting a topological basis whose preimages under a continuous surjection are compact
is prespectral: every basis member equals the image of its compact preimage. -/
theorem prespectralSpace_of_isTopologicalBasis_of_surjective {f : X → Y} {B : Set (Set Y)}
    (hB : IsTopologicalBasis B) (hsurj : Function.Surjective f) (hf : Continuous f)
    (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : PrespectralSpace Y :=
  .of_isTopologicalBasis hB fun b hb ↦ by
    rw [← image_preimage_eq b hsurj]
    exact (hpre b hb).image hf

/-- A continuous surjection from a quasiseparated space transfers quasiseparatedness to any target
admitting a topological basis with compact preimages. -/
theorem quasiSeparatedSpace_of_isTopologicalBasis_of_surjective [QuasiSeparatedSpace X]
    {f : X → Y} {B : Set (Set Y)} (hB : IsTopologicalBasis B) (hsurj : Function.Surjective f)
    (hf : Continuous f) (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : QuasiSeparatedSpace Y := by
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun b : B ↦ b.1)
    (by simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hB) fun b₁ b₂ ↦ ?_
  rw [← image_preimage_eq (b₁.1 ∩ b₂.1) hsurj, preimage_inter]
  exact ((hpre b₁.1 b₁.2).inter_of_isOpen (hpre b₂.1 b₂.2)
    ((hB.isOpen b₁.2).preimage hf) ((hB.isOpen b₂.2).preimage hf)).image hf

/-- A continuous surjection from a compact, quasi-sober, quasiseparated prespectral space transfers
quasi-sobriety to any target admitting a topological basis with compact preimages. -/
theorem quasiSober_of_isTopologicalBasis_of_surjective [CompactSpace X] [QuasiSober X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] {f : X → Y} {B : Set (Set Y)}
    (hB : IsTopologicalBasis B) (hsurj : Function.Surjective f) (hf : Continuous f)
    (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : QuasiSober Y := by
  let g : WithConstructibleTopology X → Y := f ∘ WithTopology.ofTopology
  have hg_surj : Function.Surjective g := hsurj.comp (WithTopology.ofTopology_surjective _)
  have hcomp : @CompactSpace Y (TopologicalSpace.coinduced g inferInstance) :=
    @Function.Surjective.compactSpace _ _ _ (TopologicalSpace.coinduced g inferInstance) g
      continuous_coinduced_rng inferInstance hg_surj
  refine quasiSober_of_isClopen_generateFrom (t' := TopologicalSpace.coinduced g inferInstance)
    hB.eq_generateFrom hcomp fun b hb ↦ ?_
  have hcl : IsClopen (g ⁻¹' b) :=
    (hpre b hb).isClopen_preimage_ofTopology_of_isOpen ((hB.isOpen hb).preimage hf)
  exact ⟨isClosed_coinduced.mpr hcl.isClosed, isOpen_coinduced.mpr hcl.isOpen⟩

/-- **Target spectrality from a basis with compact preimages.** If `f : X → Y` is a continuous
surjection from a compact, quasi-sober, quasiseparated prespectral space onto a `T0Space` `Y`, and
`Y` has a topological basis whose members pull back to compact subsets of `X`, then `Y` is a
spectral space. Note that `X` itself need not be `T0Space`. -/
theorem spectralSpace_of_isTopologicalBasis_of_surjective [CompactSpace X] [QuasiSober X]
    [PrespectralSpace X] [QuasiSeparatedSpace X] [T0Space Y] {f : X → Y} {B : Set (Set Y)}
    (hB : IsTopologicalBasis B) (hsurj : Function.Surjective f) (hf : Continuous f)
    (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : SpectralSpace Y where
  toCompactSpace := hsurj.compactSpace hf
  toQuasiSober := quasiSober_of_isTopologicalBasis_of_surjective hB hsurj hf hpre
  toQuasiSeparatedSpace := quasiSeparatedSpace_of_isTopologicalBasis_of_surjective hB hsurj hf hpre
  toPrespectralSpace := prespectralSpace_of_isTopologicalBasis_of_surjective hB hsurj hf hpre

/-- Spectrality of the restriction of a map between subspaces is tested on compact open subsets of
the ambient target: every compact open subset of `V` must pull back to a compact subset of `U`. -/
theorem _root_.Set.MapsTo.isSpectralMap_restrict_iff {f : X → Y} {U : Set X} {V : Set Y}
    (hUV : MapsTo f U V) (hf : ContinuousOn f U) (hV : IsOpen V) :
    IsSpectralMap (hUV.restrict f U V) ↔
      ∀ K ⊆ V, IsOpen K → IsCompact K → IsCompact (U ∩ f ⁻¹' K) := by
  have hpre (K : Set Y) :
      Subtype.val '' (hUV.restrict f U V ⁻¹' (Subtype.val ⁻¹' K)) = U ∩ f ⁻¹' K := by
    rw [← preimage_comp, MapsTo.restrict_commutes, preimage_comp, Subtype.image_preimage_coe]
  constructor
  · intro h K hKV hKo hKc
    rw [← hpre]
    refine (h.isCompact_preimage_of_isOpen (hKo.preimage continuous_subtype_val) ?_).image
      continuous_subtype_val
    rwa [IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hKV]
  · intro h
    refine ⟨hf.mapsToRestrict hUV, fun s hso hsc ↦ ?_⟩
    rw [← preimage_image_eq s Subtype.val_injective, IsEmbedding.subtypeVal.isCompact_iff, hpre]
    exact h _ (Subtype.coe_image_subset V s) (hV.isOpenMap_subtype_val s hso)
      (hsc.image continuous_subtype_val)

/-- Evaluation at a coordinate `i` is a spectral map as soon as every *other* factor is
quasi-compact: the preimage of a quasi-compact open is a box with that set in the `i`-th slot and
the whole space elsewhere, so only those other slots need a compactness hypothesis. -/
theorem isSpectralMap_eval {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] (i : ι)
    (hZ : ∀ j, j ≠ i → IsCompact (univ : Set (Z j))) :
    IsSpectralMap (fun f : ∀ i, Z i ↦ f i) where
  toContinuous := continuous_apply i
  isCompact_preimage_of_isOpen := fun U _ hUc ↦ by
    classical
    rw [Set.eval_preimage]
    refine isCompact_univ_pi fun j ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using hUc
    · rw [Function.update_of_ne hj]
      exact hZ j hj

/-- **Spectrality transports along an embedding.** A subset of the target contained in the range
of an embedding is spectral if and only if its preimage is: the embedding restricts to a
homeomorphism between the two.

This is the shape every "prove it on a subspace and carry it back" spectrality argument takes.
It is worth stating separately because the *reason* one works on the subspace is usually that the
inclusion is not a spectral map, which makes the general preservation theorems unavailable along
it; this lemma supplies the homeomorphism route instead. -/
theorem _root_.Topology.IsEmbedding.spectralSpace_preimage_iff {f : X → Y} (hf : IsEmbedding f)
    {S : Set Y} (hS : S ⊆ range f) : SpectralSpace (f ⁻¹' S) ↔ SpectralSpace S := by
  -- The embedding restricts to a homeomorphism `f ⁻¹' S ≃ₜ S`.
  let e := hf.homeomorphOfSubsetRange hS
  -- Transfer compactness along it, then spectrality; a homeomorphism is an open embedding.
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : CompactSpace S := e.compactSpace
    exact e.symm.isOpenEmbedding.spectralSpace
  · have : CompactSpace (f ⁻¹' S) := e.symm.compactSpace
    exact e.isOpenEmbedding.spectralSpace

/-- Inside a spectral open subset `V`, every point of an open set `O` has a compact spectral open
neighbourhood contained in `V ∩ O`. -/
theorem _root_.IsOpen.exists_spectralSpace_subset_inter {V O : Set X} (hVo : IsOpen V)
    (hVs : SpectralSpace V) (hOo : IsOpen O) {x : X} (hxV : x ∈ V) (hxO : x ∈ O) :
    ∃ W ⊆ V ∩ O, IsOpen W ∧ x ∈ W ∧ IsCompact W ∧ SpectralSpace W := by
  obtain ⟨W', ⟨hW'o, hW'c⟩, hxW', hW'O⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (a := (⟨x, hxV⟩ : V))
      (mem_preimage.2 hxO) (hOo.preimage continuous_subtype_val)
  have hemb := hVo.isOpenEmbedding_subtypeVal
  refine ⟨Subtype.val '' W', ?_, hemb.isOpenMap _ hW'o, ⟨_, hxW', rfl⟩,
    hW'c.image continuous_subtype_val, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hW'O hy⟩
  · refine (hemb.isEmbedding.spectralSpace_preimage_iff (image_subset_range _ _)).mp ?_
    rw [preimage_image_eq W' Subtype.val_injective]
    have : CompactSpace W' := isCompact_iff_compactSpace.mp hW'c
    exact hW'o.isOpenEmbedding_subtypeVal.spectralSpace

/-- The Sierpiński space `Prop` is spectral. -/
theorem spectralSpace_prop : SpectralSpace Prop := by
  have hF {p : Prop} (hp : p ∉ ({True} : Set Prop)) : p = False :=
    eq_false fun h ↦ hp (eq_true h)
  have hT0 : T0Space Prop := (t0Space_iff_inseparable Prop).mpr fun p q h ↦
    propext (by simpa using h.mem_open_iff isOpen_singleton_true)
  have hsober : QuasiSober Prop := by
    refine (quasiSober_iff Prop).mpr fun {S} hS hSc ↦ ?_
    by_cases hT : True ∈ S
    · -- `True` specializes to every point: it is generic in each closed set containing it.
      refine ⟨True, isGenericPoint_iff_specializes.mpr fun y ↦
        ⟨fun h ↦ h.mem_closed hSc hT, fun _ ↦ ?_⟩⟩
      by_cases hy : y
      · rw [eq_true hy]
      · rw [eq_false hy, specializes_iff_nhds, nhds_false]
        exact le_top
    · -- Otherwise every point of `S` is `False`, which is then the generic point.
      have hSF {p : Prop} (hp : p ∈ S) : p = False :=
        hF fun h ↦ hT (mem_singleton_iff.mp h ▸ hp)
      obtain ⟨p, hp⟩ := hS.nonempty
      refine ⟨False, isGenericPoint_iff_specializes.mpr fun y ↦ ⟨fun h ↦ ?_, fun hy ↦ ?_⟩⟩
      · rw [hF fun hy ↦ false_ne_true (mem_singleton_iff.mp (h.mem_open isOpen_singleton_true hy)),
          ← hSF hp]
        exact hp
      · rw [hSF hy]
  exact {}

/-- An open embedding from a compact space to a quasiseparated space is spectral. -/
theorem _root_.Topology.IsOpenEmbedding.isSpectralMap [CompactSpace X] [QuasiSeparatedSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) : IsSpectralMap f := by
  refine ⟨hf.continuous, fun s hso hsc ↦ ?_⟩
  rw [hf.isEmbedding.isCompact_iff, image_preimage_eq_inter_range]
  exact hsc.inter_of_isOpen (by simpa only [image_univ] using isCompact_univ.image hf.continuous)
    hso hf.isOpen_range

/-- The full subspace of a spectral space is spectral. -/
theorem spectralSpace_univ [SpectralSpace X] : SpectralSpace (Set.univ : Set X) := by
  let _ : CompactSpace (univ : Set X) := (Homeomorph.Set.univ X).symm.compactSpace
  exact isOpen_univ.isOpenEmbedding_subtypeVal.spectralSpace

end TauCeti

end
