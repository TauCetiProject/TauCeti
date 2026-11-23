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
* `IsProperMap.pullback_snd`: proper maps are stable under base change along continuous maps.
* `IsProperMap.exists_tendsto_of_tendsto_apply_prodMk`: ultrafilter convergence for a proper map
  `h : T × Y → W` evaluated at a variable first coordinate `φ z` that is continuous away from a
  set `A` where `t ↦ h (t, y)` is independent of `t`.
* `TauCeti.isProperMap_subtypeVal_iff`, `TauCeti.isProperMap_prodMk_left`,
  `TauCeti.isProperMap_prodMk_right`: properness of subspace inclusions and of sections into a
  product.
* `TauCeti.isProperMap_iff_domRestrict_of_iUnion_eq_univ` and
  `IsClosed.isProperMap_iff_domRestrict_of_union_eq_univ`: a map whose source is covered by
  finitely many closed sets is proper if and only if its restriction to each piece is proper.
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

/-- **Proper maps are stable under base change.** If `f : X → Y` is proper and `g : Z → Y` is
continuous, the projection from the fiber product `X ×_Y Z` to `Z` is proper. The fiber product is
the preimage of the graph of `g` under the proper map `Prod.map f id`. -/
theorem IsProperMap.pullback_snd {f : X → Y} {g : Z → Y} (hf : IsProperMap f)
    (hg : Continuous g) : IsProperMap (Function.Pullback.snd : f.Pullback g → Z) := by
  refine (hf.prodMap isProperMap_id).of_isEmbedding_of_range_eq IsEmbedding.subtypeVal
    (Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ ↦ rfl) continuous_snd
      (hg.prodMk continuous_id)) (funext fun p ↦ Prod.ext p.property rfl) ?_
  ext ⟨x, z⟩
  constructor
  · rintro ⟨p, hp⟩
    rw [← hp]
    exact ⟨p.val.2, Prod.ext p.property.symm rfl⟩
  · rintro ⟨z', h⟩
    obtain rfl : z' = z := congrArg Prod.snd h
    exact ⟨⟨(x, z'), (congrArg Prod.fst h).symm⟩, rfl⟩

/-- **Ultrafilter convergence for a proper map evaluated at a variable first coordinate.** If
`h : T × Y → W` is proper with `T` Hausdorff, `t ↦ h (t, y)` is independent of `t` for `y ∈ A`,
`φ : Z → T` is continuous away from `q ⁻¹' A`, and `h (φ z, q z)` tends to `w₀` along an
ultrafilter `𝒰`, then `q` tends along `𝒰` to some `y₁` such that `h (φ z₁, q z₁) = w₀` at every
cluster limit `z₁` of `𝒰` with `q z₁ = y₁`. -/
theorem IsProperMap.exists_tendsto_of_tendsto_apply_prodMk {T : Type*} [TopologicalSpace T]
    [T2Space T] {h : T × Y → W} (hh : IsProperMap h) {A : Set Y}
    (hA : ∀ t₁ t₂, ∀ y ∈ A, h (t₁, y) = h (t₂, y)) {q : Z → Y} {φ : Z → T}
    (hφ : ∀ z, q z ∉ A → ContinuousAt φ z) {𝒰 : Ultrafilter Z} {w₀ : W}
    (hw₀ : Tendsto (fun z ↦ h (φ z, q z)) 𝒰 (𝓝 w₀)) :
    ∃ y₁, Tendsto q 𝒰 (𝓝 y₁) ∧
      ∀ z₁ : Z, q z₁ = y₁ → (𝒰 : Filter Z) ≤ 𝓝 z₁ → h (φ z₁, q z₁) = w₀ := by
  have hmap : Tendsto h (Ultrafilter.map (fun z ↦ (φ z, q z)) 𝒰) (𝓝 w₀) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact hw₀
  obtain ⟨⟨t₁, y₁⟩, hty₁, hle⟩ := hh.ultrafilter_le_nhds_of_tendsto hmap
  rw [Ultrafilter.coe_map, nhds_prod_eq, ← Tendsto, tendsto_prod_iff'] at hle
  refine ⟨y₁, hle.2, fun z₁ hqz₁ hz₁ ↦ ?_⟩
  by_cases hy₁A : y₁ ∈ A
  · rw [hqz₁, hA (φ z₁) t₁ _ hy₁A, hty₁]
  · have hqz₁A : q z₁ ∉ A := hqz₁ ▸ hy₁A
    have hφ_eq : φ z₁ = t₁ := tendsto_nhds_unique ((hφ z₁ hqz₁A).mono_left hz₁) hle.1
    rw [hφ_eq, hqz₁, hty₁]

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
  refine ⟨hf.comp continuous_subtypeVal, fun C hC ↦ ?_, fun y ↦ ?_⟩
  · have himage : (fun x : ↥(⋃ i ∈ s, S i) ↦ f x) '' C =
        ⋃ i : s, (fun x : S i.val ↦ f x) ''
          (Set.inclusion (Set.subset_biUnion_of_mem (u := S) i.property) ⁻¹' C) := by
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
      (hSf i.val i.property).isClosedMap _
        (hC.preimage (Continuous.subtype_mk continuous_subtypeVal _))
  · have hfib : (fun x : ↥(⋃ i ∈ s, S i) ↦ f x) ⁻¹' {y} =
        ⋃ i : s, Set.inclusion (Set.subset_biUnion_of_mem (u := S) i.property) ''
          ((fun x : S i.val ↦ f x) ⁻¹' {y}) := by
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
      ((hSf i.val i.property).isCompact_preimage isCompact_singleton).image
        (Continuous.subtype_mk continuous_subtypeVal _)

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

namespace TauCeti

/-- The inclusion of a subset `s ⊆ X` is proper if and only if `s` is closed. -/
@[simp]
theorem isProperMap_subtypeVal_iff {s : Set X} : IsProperMap ((↑) : s → X) ↔ IsClosed s :=
  ⟨fun h ↦ Subtype.range_coe (s := s) ▸ h.isClosed_range, IsClosed.isProperMap_subtypeVal⟩

/-- In a `T₁` space `X`, the section `y ↦ (x, y)` into `X × Y` is proper. -/
theorem isProperMap_prodMk_left [T1Space X] (x : X) : IsProperMap (fun y : Y ↦ (x, y)) :=
  isProperMap_of_isClosedMap_of_inj (.prodMk_right x) (Prod.mk_right_injective x)
    (isClosedMap_prodMk_left x)

/-- In a `T₁` space `Y`, the section `x ↦ (x, y)` into `X × Y` is proper. -/
theorem isProperMap_prodMk_right [T1Space Y] (y : Y) : IsProperMap (fun x : X ↦ (x, y)) :=
  isProperMap_of_isClosedMap_of_inj (.prodMk_left y) (Prod.mk_left_injective y)
    (isClosedMap_prodMk_right y)

/-- **Properness on a finite closed cover of the source.** If finitely many closed sets `s i` cover
`X`, then `f : X → Y` is proper if and only if its restriction `Set.domRestrict (s i) f` to each
piece is proper. -/
theorem isProperMap_iff_domRestrict_of_iUnion_eq_univ {ι : Type*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, IsClosed (s i)) (hcov : ⋃ i, s i = Set.univ) :
    IsProperMap f ↔ ∀ i, IsProperMap ((s i).domRestrict f) := by
  refine ⟨fun hf i ↦ hf.restrict (hs i), fun hall ↦ ?_⟩
  have hpre (D : Set Y) :
      f ⁻¹' D = ⋃ i, ((↑) : s i → X) '' ((s i).domRestrict f ⁻¹' D) := by
    simp_rw [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe, ← Set.iUnion_inter,
      hcov, Set.univ_inter]
  refine isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨?_, ?_, ?_⟩
  · refine continuous_iff_isClosed.2 fun D hD ↦ ?_
    rw [hpre]
    exact isClosed_iUnion_of_finite fun i ↦
      (hs i).isClosedEmbedding_subtypeVal.isClosedMap _ (hD.preimage (hall i).continuous)
  · intro E hE
    have himg : f '' E = ⋃ i, (s i).domRestrict f '' (((↑) : s i → X) ⁻¹' E) := by
      simp_rw [Set.image_domRestrict, ← Set.image_iUnion, ← Set.inter_iUnion, hcov, Set.inter_univ]
    rw [himg]
    exact isClosed_iUnion_of_finite fun i ↦
      (hall i).isClosedMap _ (hE.preimage continuous_subtypeVal)
  · intro y
    rw [hpre]
    exact isCompact_iUnion fun i ↦
      ((hall i).isCompact_preimage isCompact_singleton).image continuous_subtypeVal

/-- **Properness on a binary closed cover of the source.** If closed sets `s` and `t` cover `X`,
then `f : X → Y` is proper if and only if its restrictions to `s` and to `t` are proper. -/
theorem _root_.IsClosed.isProperMap_iff_domRestrict_of_union_eq_univ {s t : Set X} (hs : IsClosed s)
    (ht : IsClosed t) (hst : s ∪ t = Set.univ) :
    IsProperMap f ↔ IsProperMap (s.domRestrict f) ∧ IsProperMap (t.domRestrict f) := by
  have hcov : (⋃ b : Bool, cond b s t) = Set.univ := Set.union_eq_iUnion.symm.trans hst
  rw [isProperMap_iff_domRestrict_of_iUnion_eq_univ (fun b ↦ by cases b <;> assumption) hcov,
    Bool.forall_bool, Bool.cond_true, Bool.cond_false, and_comm]

end TauCeti
