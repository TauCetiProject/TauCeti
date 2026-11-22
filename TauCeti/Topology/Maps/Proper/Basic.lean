/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper maps: compact domains, composition with homeomorphisms, products and pullbacks

Composing with a homeomorphism on either side neither creates nor destroys properness, in the
pattern of Mathlib's `Homeomorph.comp_isOpenMap_iff`.

Mathlib's `IsProperMap.prodMap` says that a product of two proper maps is proper. This file
proves the converse: if `Prod.map f g` is proper and the source of `g` is nonempty, then `f` is
proper, and symmetrically. No separation axiom is needed. An ultrafilter on the source of `f`
along which `f` converges is pushed into the product along a slice `x ↦ (x, z)`, and a limit of
the pushed ultrafilter projects to a limit of the original one.

The nonemptiness hypotheses cannot be dropped: a map out of an empty space is proper, so
`Prod.map f g` is proper for every `f` when the source of `g` is empty.

## Main declarations

* `IsProperMap.compactSpace` and `IsProperMap.sigmaCompactSpace`: the domain of a proper map to a
  compact (respectively sigma-compact) space is compact (respectively sigma-compact).
* `Homeomorph.comp_isProperMap_iff` and `Homeomorph.comp_isProperMap_iff'`: properness is
  invariant under composition with a homeomorphism.
* `IsProperMap.of_prodMap_left` and `IsProperMap.of_prodMap_right`: the factors of a proper
  product map with nonempty sources are proper.
* `isProperMap_prodMap_iff`: for nonempty sources, `Prod.map f g` is proper exactly when `f` and
  `g` are.
* `IsProperMap.of_isEmbedding_of_range_eq`: the pullback of a proper map along an embedding of its
  codomain is proper. This is Mathlib's `IsProperMap.restrictPreimage`, stated for a square of
  embeddings rather than for subtypes.
* `Continuous.isClosedEmbedding_fst_prod`: a parameter-preserving map `(p, x) ↦ (p, G (p, x))`
  with injective slices, compact second factor and Hausdorff target is a closed embedding.
* `Continuous.isProperMap_restrict_biUnion` and `Continuous.isProperMap_restrict_union`: a
  continuous map that is proper on each member of a finite family of subsets is proper on their
  union.
-/

public section

open Filter Topology

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

namespace Homeomorph

/-- Postcomposing with a homeomorphism neither creates nor destroys properness. -/
@[simp]
theorem comp_isProperMap_iff (h : X ≃ₜ Y) {f : Z → X} : IsProperMap (h ∘ f) ↔ IsProperMap f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ h.isProperMap.comp hf⟩
  rw [← Function.id_comp f, ← h.symm_comp_self, Function.comp_assoc]
  exact h.symm.isProperMap.comp hf

/-- Precomposing with a homeomorphism neither creates nor destroys properness. -/
@[simp]
theorem comp_isProperMap_iff' (h : X ≃ₜ Y) {f : Y → Z} : IsProperMap (f ∘ h) ↔ IsProperMap f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp h.isProperMap⟩
  rw [← Function.comp_id f, ← h.self_comp_symm, ← Function.comp_assoc]
  exact hf.comp h.symm.isProperMap

end Homeomorph

variable {f : X → Y} {g : Z → W}

/-- The domain of a proper map to a compact space is compact. No separation axiom is needed. -/
theorem IsProperMap.compactSpace [CompactSpace Y] (hf : IsProperMap f) : CompactSpace X := by
  refine ⟨?_⟩
  simpa only [Set.preimage_univ] using
    hf.isCompact_preimage (isCompact_univ : IsCompact (Set.univ : Set Y))

/-- The domain of a proper map to a sigma-compact space is sigma-compact. No separation axiom is
needed. -/
theorem IsProperMap.sigmaCompactSpace [SigmaCompactSpace Y] (hf : IsProperMap f) :
    SigmaCompactSpace X := by
  refine ⟨⟨fun n ↦ f ⁻¹' compactCovering Y n,
    fun n ↦ hf.isCompact_preimage (isCompact_compactCovering Y n), ?_⟩⟩
  rw [← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ]

/-- If a product map `Prod.map f g` is proper and the source of `g` is nonempty, then `f` is
proper. -/
theorem IsProperMap.of_prodMap_left [Nonempty Z] (h : IsProperMap (Prod.map f g)) :
    IsProperMap f := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  rw [isProperMap_iff_ultrafilter] at h ⊢
  refine ⟨continuous_fst.comp (h.1.comp (Continuous.prodMk_left z)), fun 𝒰 y hy ↦ ?_⟩
  -- Push `𝒰` into the product along the slice through `z`.
  obtain ⟨⟨x, z'⟩, hxz, hx⟩ := h.2 (𝒰 := 𝒰.map fun x ↦ (x, z)) (y := (y, g z))
    (hy.prodMk_nhds tendsto_const_nhds)
  refine ⟨x, congrArg Prod.fst hxz, ?_⟩
  have hfst := (continuous_fst.tendsto (x, z')).mono_left hx
  rw [Ultrafilter.coe_map, tendsto_map'_iff] at hfst
  exact tendsto_id'.1 hfst

/-- If a product map `Prod.map f g` is proper and the source of `f` is nonempty, then `g` is
proper. -/
theorem IsProperMap.of_prodMap_right [Nonempty X] (h : IsProperMap (Prod.map f g)) :
    IsProperMap g := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rw [isProperMap_iff_ultrafilter] at h ⊢
  refine ⟨continuous_snd.comp (h.1.comp (Continuous.prodMk_right x)), fun 𝒰 w hw ↦ ?_⟩
  -- Push `𝒰` into the product along the slice through `x`.
  obtain ⟨⟨x', z⟩, hxz, hz⟩ := h.2 (𝒰 := 𝒰.map fun z ↦ (x, z)) (y := (f x, w))
    (tendsto_const_nhds.prodMk_nhds hw)
  refine ⟨z, congrArg Prod.snd hxz, ?_⟩
  have hsnd := (continuous_snd.tendsto (x', z)).mono_left hz
  rw [Ultrafilter.coe_map, tendsto_map'_iff] at hsnd
  exact tendsto_id'.1 hsnd

/-- For nonempty sources, a product map `Prod.map f g` is proper exactly when both `f` and `g`
are proper. -/
@[simp]
theorem isProperMap_prodMap_iff [Nonempty X] [Nonempty Z] :
    IsProperMap (Prod.map f g) ↔ IsProperMap f ∧ IsProperMap g :=
  ⟨fun h ↦ ⟨h.of_prodMap_left, h.of_prodMap_right⟩, fun h ↦ h.1.prodMap h.2⟩

/-- **The pullback of a proper map along an embedding is proper.** If `f ∘ i = j ∘ f'`, where
`i` and `j` are embeddings and the range of `i` is the preimage under `f` of the range of `j`,
then `f'` is proper. -/
theorem IsProperMap.of_isEmbedding_of_range_eq {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {f' : X' → Y'} {i : X' → X} {j : Y' → Y} (hf : IsProperMap f)
    (hi : IsEmbedding i) (hj : IsEmbedding j) (hcomm : f ∘ i = j ∘ f')
    (hrange : Set.range i = f ⁻¹' Set.range j) : IsProperMap f' := by
  refine isProperMap_iff_ultrafilter.mpr ⟨hj.continuous_iff.mpr
    (hcomm ▸ hf.continuous.comp hi.continuous), fun 𝒰 y' h ↦ ?_⟩
  -- Push `𝒰` forward along `i`, take a limit for `f`, and pull it back along `i`.
  have hmap : Tendsto f (𝒰.map i) (𝓝 (j y')) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff, hcomm]
    exact hj.continuous.continuousAt.tendsto.comp h
  obtain ⟨x, hx, hle⟩ := hf.ultrafilter_le_nhds_of_tendsto hmap
  obtain ⟨x', rfl⟩ : x ∈ Set.range i := hrange ▸ ⟨y', hx.symm⟩
  refine ⟨x', hj.injective ?_, ?_⟩
  · rw [← hx]
    exact (congrFun hcomm x').symm
  · rw [hi.nhds_eq_comap, ← map_le_iff_le_comap]
    exact hle

/-- A parameter-preserving map `(p, x) ↦ (p, G (p, x))` whose slices are injective, from a
product with a compact second factor to a Hausdorff space, is a closed embedding. Its image is the
projection along the compact factor of a closed set, so it is closed. This applies to the track of
an isotopy of a compact space, run over any parameter space. -/
theorem Continuous.isClosedEmbedding_fst_prod {P : Type*} [TopologicalSpace P] [CompactSpace X]
    [T2Space Y] {G : P × X → Y} (hG : Continuous G)
    (hinj : ∀ p, Function.Injective fun x => G (p, x)) :
    IsClosedEmbedding fun q : P × X => (q.1, G q) := by
  refine .of_continuous_injective_isClosedMap (continuous_fst.prodMk hG) ?_ ?_
  · rintro ⟨p, x⟩ ⟨p', x'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact Prod.ext rfl (hinj p h)
  · intro C hC
    -- The image is the projection along `X` of a closed subset of `(P × Y) × X`.
    have himage : (fun q : P × X => (q.1, G q)) '' C =
        Prod.fst '' {r : (P × Y) × X | (r.1.1, r.2) ∈ C ∧ G (r.1.1, r.2) = r.1.2} := by
      ext ⟨p, y⟩
      constructor
      · rintro ⟨⟨p', x⟩, hx, h⟩
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨((p', G (p', x)), x), ⟨hx, rfl⟩, rfl⟩
      · rintro ⟨⟨⟨p', y'⟩, x⟩, ⟨hx, hy⟩, h⟩
        simp only [Prod.mk.injEq] at h hy
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨(p', x), hx, by simp [hy]⟩
    rw [himage]
    exact isClosedMap_fst_of_compactSpace _
      ((hC.preimage (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop)))

/-- If `f : X → Y` is continuous and proper on each member of a finite family `S`, then `f`
is proper on `⋃ i ∈ s, S i`. No separation axiom is needed. -/
theorem Continuous.isProperMap_restrict_biUnion {ι : Type*} (s : Finset ι) (S : ι → Set X)
    (hf : Continuous f) (hSf : ∀ i ∈ s, IsProperMap fun x : S i ↦ f x) :
    IsProperMap fun x : ↥(⋃ i ∈ s, S i) ↦ f x := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf.comp continuous_subtype_val, fun C hC ↦ ?_, fun y ↦ ?_⟩
  · have himage : (fun x : ↥(⋃ i ∈ s, S i) ↦ f x) '' C =
        ⋃ i : s, (fun x : S i.1 ↦ f x) ''
          (Set.inclusion (Set.subset_biUnion_of_mem (u := S) i.2) ⁻¹' C) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨x, hx⟩, hxC, hxy⟩
        rcases Set.mem_iUnion₂.1 hx with ⟨i, hi, hxi⟩
        exact ⟨⟨i, hi⟩, ⟨x, hxi⟩, hxC, hxy⟩
      · rintro ⟨⟨i, hi⟩, ⟨x, hxi⟩, hxC, hxy⟩
        exact ⟨⟨x, Set.mem_biUnion hi hxi⟩, hxC, hxy⟩
    rw [himage]
    exact isClosed_iUnion_of_finite fun i : s ↦
      (hSf i.1 i.2).isClosedMap _ (hC.preimage (Continuous.subtype_mk continuous_subtype_val _))
  · have hfib : (fun x : ↥(⋃ i ∈ s, S i) ↦ f x) ⁻¹' {y} =
        ⋃ i : s, Set.inclusion (Set.subset_biUnion_of_mem (u := S) i.2) ''
          ((fun x : S i.1 ↦ f x) ⁻¹' {y}) := by
      ext ⟨x, hx⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image]
      refine ⟨?_, ?_⟩
      · intro hxy
        rcases Set.mem_iUnion₂.1 hx with ⟨i, hi, hxi⟩
        exact ⟨⟨i, hi⟩, ⟨x, hxi⟩, hxy, rfl⟩
      · rintro ⟨⟨i, hi⟩, ⟨x', hx'⟩, hxy, heq⟩
        obtain rfl : x' = x := congrArg Subtype.val heq
        exact hxy
    rw [hfib]
    exact isCompact_iUnion fun i : s ↦
      ((hSf i.1 i.2).isCompact_preimage isCompact_singleton).image
        (Continuous.subtype_mk continuous_subtype_val _)

/-- If `f : X → Y` is continuous and proper on subsets `S₁` and `S₂`, then `f` is proper on
`S₁ ∪ S₂`. No separation axiom is needed. -/
theorem Continuous.isProperMap_restrict_union {S₁ S₂ : Set X} (hf : Continuous f)
    (hf₁ : IsProperMap fun x : S₁ ↦ f x) (hf₂ : IsProperMap fun x : S₂ ↦ f x) :
    IsProperMap fun x : ↥(S₁ ∪ S₂) ↦ f x := by
  let S : Bool → Set X := Bool.rec S₂ S₁
  have hcover : (⋃ b ∈ (Finset.univ : Finset Bool), S b) = S₁ ∪ S₂ := by
    ext x
    simp [S, Bool.exists_bool, or_comm]
  exact (hf.isProperMap_restrict_biUnion Finset.univ S fun b _ ↦ Bool.casesOn b hf₂ hf₁).comp
    (Homeomorph.setCongr hcover.symm).isProperMap

