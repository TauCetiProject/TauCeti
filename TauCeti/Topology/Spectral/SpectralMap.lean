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
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.WithTopology
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# A basis criterion for spectral maps, and transport of spectrality along an embedding

Utilities for spectral spaces and maps. A continuous map is spectral as soon as the preimage
of every member of some topological **basis** of the target is compact; and a set contained in the
range of an embedding is spectral exactly when its preimage is.

The basis criterion first. Spectrality asks for compact preimages of all compact open sets; the
reduction to a basis is the observation that a compact open set is a *finite* union of basis
elements — cover it by the basis members it contains and extract a finite subcover — and a finite
union of compact preimages is compact.

Nothing is assumed of the basis members themselves, not even compactness: only their preimages
enter the argument. In the intended applications the basis members are the distinguished
quasi-compact opens of a spectral space (Wedhorn's family `R` for `Spv (A, I)`), whose preimages
are computed by hand.

Mathlib's `IsSpectralMap` API provides constructors from identities, compositions and embeddings,
but no criterion that tests spectrality on a basis; this supplies the missing entry point.

## Main results

* `TauCeti.isSpectralMap_of_isTopologicalBasis` : a continuous map whose preimages of basis
  members are compact is a spectral map.
* `Set.MapsTo.isSpectralMap_restrict_iff`: spectrality of a restriction expressed in terms of
  subsets of the ambient spaces.
* `TauCeti.isSpectralMap_eval`: a coordinate projection is spectral when every other factor
  is quasi-compact.
* `TauCeti.isSpectralMap_prodMk_left`, `TauCeti.isSpectralMap_prodMk_right`: horizontal and
  vertical slices into a product are spectral maps.
* `IsSpectralMap.quasiSeparatedSpace_of_surjective`: a surjective spectral map transfers
  quasiseparatedness to its target.
* `PrespectralSpace.prod`, `QuasiSeparatedSpace.prod`, `SpectralSpace.prod`: binary products
  of prespectral, quasiseparated prespectral, and spectral spaces.
* `Topology.IsEmbedding.spectralSpace_preimage_iff` : a subset of the range of an embedding is
  spectral if and only if its preimage is — the transport step of any "prove it on a subspace"
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

/-- Fixing the second coordinate gives a spectral map `x ↦ (x, y)` for arbitrary topological
spaces `X` and `Y`. -/
theorem isSpectralMap_prodMk_left (y : Y) : IsSpectralMap (fun x : X ↦ (x, y)) := by
  refine ⟨Continuous.prodMk_left y, fun W hWo hWc ↦ isCompact_iff_finite_subcover.mpr ?_⟩
  intro ι U hUo hUcov
  let V : Set (X × Y) := ⋃₀ {O : Set (X × Y) | IsOpen O ∧ O ⊆ W ∧ ∀ x, (x, y) ∉ O}
  have hVo : IsOpen V := isOpen_sUnion fun _ hO ↦ hO.1
  have hWdiff : W \ V ⊆ ⋃ i, U i ×ˢ univ := by
    rintro ⟨x', y'⟩ ⟨hW, hV⟩
    by_cases hxy : (x', y) ∈ W
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcov hxy)
      exact mem_iUnion.mpr ⟨i, hi, trivial⟩
    · exfalso
      obtain ⟨A, B, hAo, hBo, hx'A, hy'B, hABW⟩ := isOpen_prod_iff.mp hWo x' y' hW
      refine hV (mem_sUnion.mpr ⟨A ×ˢ B,
        ⟨hAo.prod hBo, hABW, fun _ hxy' ↦ hxy (hABW ⟨hx'A, hxy'.2⟩)⟩, hx'A, hy'B⟩)
  obtain ⟨t, ht⟩ := (hWc.diff hVo).elim_finite_subcover (fun i ↦ U i ×ˢ univ)
    (fun i ↦ (hUo i).prod isOpen_univ) hWdiff
  refine ⟨t, fun x hxW ↦ ?_⟩
  have hxV : (x, y) ∉ V := by
    rintro ⟨O, ⟨_, _, hO⟩, hxO⟩
    exact hO x hxO
  obtain ⟨i, hi, hxU, -⟩ := mem_iUnion₂.mp (ht ⟨hxW, hxV⟩)
  exact mem_iUnion₂.mpr ⟨i, hi, hxU⟩

/-- Fixing the first coordinate gives a spectral map `y ↦ (x, y)` for arbitrary topological spaces
`X` and `Y`. -/
theorem isSpectralMap_prodMk_right (x : X) : IsSpectralMap (fun y : Y ↦ (x, y)) :=
  (Homeomorph.prodComm Y X).isProperMap.isSpectralMap.comp (isSpectralMap_prodMk_left x)

/-- A surjective spectral map out of a quasiseparated space makes its target quasiseparated. -/
theorem _root_.IsSpectralMap.quasiSeparatedSpace_of_surjective [QuasiSeparatedSpace X]
    {f : X → Y} (hf : IsSpectralMap f) (hsurj : Function.Surjective f) :
    QuasiSeparatedSpace Y where
  inter_isCompact U V hUo hUc hVo hVc := by
    rw [← Set.image_preimage_eq (U ∩ V) hsurj, Set.preimage_inter]
    exact ((hf.isCompact_preimage_of_isOpen hUo hUc).inter_of_isOpen
      (hf.isCompact_preimage_of_isOpen hVo hVc) (hUo.preimage hf.continuous)
      (hVo.preimage hf.continuous)).image hf.continuous

/-- The product of two prespectral spaces is prespectral. -/
instance _root_.PrespectralSpace.prod [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace (X × Y) := by
  refine .of_isTopologicalBasis
    (PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis) ?_
  rintro _ ⟨U, ⟨_, hUc⟩, V, ⟨_, hVc⟩, rfl⟩
  exact hUc.prod hVc

/-- The product of two quasiseparated prespectral spaces is quasiseparated. -/
theorem _root_.QuasiSeparatedSpace.prod [PrespectralSpace X] [PrespectralSpace Y]
    [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] : QuasiSeparatedSpace (X × Y) := by
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun p : {U : Set X // IsOpen U ∧ IsCompact U} ×
      {V : Set Y // IsOpen V ∧ IsCompact V} ↦ p.1.1 ×ˢ p.2.1) ?_ ?_
  · have hb := PrespectralSpace.isTopologicalBasis (X := X) |>.prod
      (PrespectralSpace.isTopologicalBasis (X := Y))
    convert hb using 1
    ext W
    simp [Set.range, Set.image2, Subtype.exists, eq_comm]
  · rintro ⟨⟨U₁, hU₁o, hU₁c⟩, ⟨V₁, hV₁o, hV₁c⟩⟩
      ⟨⟨U₂, hU₂o, hU₂c⟩, ⟨V₂, hV₂o, hV₂c⟩⟩
    rw [Set.prod_inter_prod]
    exact (hU₁c.inter_of_isOpen hU₂c hU₁o hU₂o).prod
      (hV₁c.inter_of_isOpen hV₂c hV₁o hV₂o)

/-- The product of two spectral spaces is spectral. -/
instance _root_.SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  have hb := PrespectralSpace.isTopologicalBasis (X := X) |>.prod
    (PrespectralSpace.isTopologicalBasis (X := Y))
  have hgen := hb.eq_generateFrom
  have hT0 : T0Space (X × Y) := inferInstance
  let tOrig : TopologicalSpace (X × Y) := inferInstance
  let t' : TopologicalSpace (X × Y) :=
    @instTopologicalSpaceProd X Y (constructibleTopology X) (constructibleTopology Y)
  have hcompX : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
      (constructibleTopology X) WithTopology.ofTopology
      (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have hcompY : @CompactSpace Y (constructibleTopology Y) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology Y) Y _
      (constructibleTopology Y) WithTopology.ofTopology
      (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have hc : @CompactSpace (X × Y) t' :=
    @instCompactSpaceProd X Y (constructibleTopology X) (constructibleTopology Y) hcompX hcompY
  refine @spectralSpace_of_isClopen_generateFrom _ _ t' tOrig hgen hc ?_ hT0
  rintro _ ⟨U, ⟨hUo, hUc⟩, V, ⟨hVo, hVc⟩, rfl⟩
  have hU : @IsClopen (X × Y) t' (Prod.fst ⁻¹' U) :=
    @IsClopen.preimage _ _ t' (constructibleTopology X) _
      (hUc.isClopen_constructibleTopology_of_isOpen hUo) Prod.fst
      (@continuous_fst X Y (constructibleTopology X) (constructibleTopology Y))
  have hV : @IsClopen (X × Y) t' (Prod.snd ⁻¹' V) :=
    @IsClopen.preimage _ _ t' (constructibleTopology Y) _
      (hVc.isClopen_constructibleTopology_of_isOpen hVo) Prod.snd
      (@continuous_snd X Y (constructibleTopology X) (constructibleTopology Y))
  dsimp only
  rw [Set.prod_eq]
  exact @IsClopen.inter (X × Y) t' _ _ hU hV

end TauCeti

end
