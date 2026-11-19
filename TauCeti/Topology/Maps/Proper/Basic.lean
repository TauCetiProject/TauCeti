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

We also record that slice inclusions `y ↦ (x, y)` and pairings `x ↦ (f x, g x)` of a proper map
with a continuous map into a Hausdorff space are proper, an ultrafilter convergence criterion for
reparametrized proper maps `z ↦ h (φ z, q z)` on products with Hausdorff first factor, and that a
map on a space covered by finitely many closed sets is proper if and only if its restriction to each
piece is proper.

## Main declarations

* `IsProperMap.compactSpace` and `IsProperMap.sigmaCompactSpace`: the domain of a proper map to a
  compact (respectively sigma-compact) space is compact (respectively sigma-compact).
* `Homeomorph.comp_isProperMap_iff` and `Homeomorph.comp_isProperMap_iff'`: properness is
  invariant under composition with a homeomorphism.
* `IsProperMap.of_prodMap_left` and `IsProperMap.of_prodMap_right`: the factors of a proper
  product map with nonempty sources are proper.
* `isProperMap_prodMap_iff`: for nonempty sources, `Prod.map f g` is proper exactly when `f` and
  `g` are.
* `isProperMap_prodMk_left` and `isProperMap_prodMk_right`: slice inclusions into a product are
  proper when the fixed factor is `T₁`.
* `IsProperMap.prodMk_of_t2_left` and `IsProperMap.prodMk_of_t2_right`: pairing a proper map with
  an arbitrary continuous map into a Hausdorff space is proper.
* `IsProperMap.exists_tendsto_of_tendsto_prodMk`: ultrafilter convergence for a reparametrized
  proper map `z ↦ h (φ z, q z)` on a product with Hausdorff first factor.
* `isProperMap_iff_iUnion_isClosed` and `isProperMap_iff_union_isClosed`: a map is proper if and
  only if its restrictions to the members of a finite closed cover are proper.
* `IsProperMap.of_isEmbedding_of_range_eq`: the pullback of a proper map along an embedding of its
  codomain is proper. This is Mathlib's `IsProperMap.restrictPreimage`, stated for a square of
  embeddings rather than for subtypes.
* `Continuous.isClosedEmbedding_fst_prod`: a parameter-preserving map `(p, x) ↦ (p, G (p, x))`
  with injective slices, compact second factor and Hausdorff target is a closed embedding.
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

/-- Including a slice `y ↦ (x, y)` into a product is proper when the first factor is `T₁`. -/
theorem isProperMap_prodMk_left [T1Space X] (x : X) : IsProperMap fun y : Y ↦ (x, y) :=
  isProperMap_of_isClosedMap_of_inj (.prodMk_right x) (Prod.mk_right_injective x)
    (isClosedMap_prodMk_left x)

/-- Including a slice `x ↦ (x, y)` into a product is proper when the second factor is `T₁`. -/
theorem isProperMap_prodMk_right [T1Space Y] (y : Y) : IsProperMap fun x : X ↦ (x, y) :=
  isProperMap_of_isClosedMap_of_inj (.prodMk_left y) (Prod.mk_left_injective y)
    (isClosedMap_prodMk_right y)

/-- Pairing a continuous map into a Hausdorff space with a proper map `g : X → Z` yields a proper
map `x ↦ (f x, g x)`. No separation axiom is needed on `X` or `Z`. -/
theorem IsProperMap.prodMk_of_t2_left {g : X → Z} [T2Space Y] (hg : IsProperMap g)
    (hf : Continuous f) : IsProperMap fun x ↦ (f x, g x) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨hf.prodMk hg.continuous, fun 𝒰 ⟨y, z⟩ hyz ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hyz
  obtain ⟨x, rfl, hx⟩ := hg.ultrafilter_le_nhds_of_tendsto hyz.2
  exact ⟨x, Prod.ext (tendsto_nhds_unique ((hf.tendsto x).mono_left hx) hyz.1) rfl, hx⟩

/-- Pairing a proper map `f : X → Y` with a continuous map into a Hausdorff space yields a proper
map `x ↦ (f x, g x)`. No separation axiom is needed on `X` or `Y`. -/
theorem IsProperMap.prodMk_of_t2_right {g : X → Z} [T2Space Z] (hf : IsProperMap f)
    (hg : Continuous g) : IsProperMap fun x ↦ (f x, g x) :=
  (Homeomorph.prodComm Z Y).isProperMap.comp (hf.prodMk_of_t2_left hg)

/-- If `h : T × Y → W` is proper with `T` Hausdorff and `z ↦ h (φ z, q z)` converges along an
ultrafilter `𝒰` to `w₀`, then `q` converges along `𝒰` to some `y₁ : Y`; moreover, at any limit
`z₀` of `𝒰` with `q z₀ = y₁` where either `φ` is continuous or `t ↦ h (t, y₁)` is constant, we
have `h (φ z₀, q z₀) = w₀`. -/
theorem IsProperMap.exists_tendsto_of_tendsto_prodMk {T : Type*} [TopologicalSpace T] [T2Space T]
    {h : T × Y → W} (hh : IsProperMap h) {φ : Z → T} {q : Z → Y} {𝒰 : Ultrafilter Z} {w₀ : W}
    (hlim : Tendsto (fun z ↦ h (φ z, q z)) 𝒰 (𝓝 w₀)) :
    ∃ y₁ : Y, Tendsto q 𝒰 (𝓝 y₁) ∧
      ∀ z₀ : Z, (𝒰 : Filter Z) ≤ 𝓝 z₀ → q z₀ = y₁ →
        (ContinuousAt φ z₀ ∨ ∀ t₁ t₂, h (t₁, y₁) = h (t₂, y₁)) →
        h (φ z₀, q z₀) = w₀ := by
  obtain ⟨⟨t₁, y₁⟩, hty, hle⟩ := hh.ultrafilter_le_nhds_of_tendsto (f := h)
    (𝒰 := 𝒰.map fun z ↦ (φ z, q z)) (by rwa [Ultrafilter.coe_map, tendsto_map'_iff])
  refine ⟨y₁, tendsto_map'_iff.1 ((continuous_snd.tendsto (t₁, y₁)).mono_left hle),
    fun z₀ hz₀ hqz hcond ↦ ?_⟩
  rcases hcond with hφ | hconst
  · have ht_lim : Tendsto φ 𝒰 (𝓝 t₁) :=
      tendsto_map'_iff.1 ((continuous_fst.tendsto (t₁, y₁)).mono_left hle)
    rw [hqz, tendsto_nhds_unique (hφ.tendsto.mono_left hz₀) ht_lim, hty]
  · rw [hqz, hconst _ t₁, hty]

/-- **Gluing proper maps along a finite closed cover.** If closed sets `s i` cover `X`, with `ι`
finite, then `f : X → Y` is proper if and only if its restriction to each `s i` is proper. Neither
continuity of `f` nor any separation axiom is assumed in advance. -/
theorem isProperMap_iff_iUnion_isClosed {ι : Type*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, IsClosed (s i)) (hcov : ⋃ i, s i = Set.univ) :
    IsProperMap f ↔ ∀ i, IsProperMap fun x : s i ↦ f x := by
  refine ⟨fun hf i ↦ hf.restrict (hs i), fun hf ↦ ?_⟩
  have hmem (x : X) : ∃ i, x ∈ s i := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ x)
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨(locallyFinite_of_finite s).continuous hcov hs
      fun i ↦ continuousOn_iff_continuous_domRestrict.2 (hf i).continuous,
    fun K hK ↦ ?_, fun y ↦ ?_⟩
  · -- The image of `K` is the finite union of its images on the pieces `s i`.
    have himage : f '' K = ⋃ i, (fun x : s i ↦ f x) '' (Subtype.val ⁻¹' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage, Subtype.exists]
      exact ⟨fun ⟨x, hxK, hfx⟩ ↦ let ⟨i, hxi⟩ := hmem x; ⟨i, x, hxi, hxK, hfx⟩,
        fun ⟨_, x, _, hxK, hfx⟩ ↦ ⟨x, hxK, hfx⟩⟩
    rw [himage]
    exact isClosed_iUnion_of_finite fun i ↦
      (hf i).isClosedMap _ (hK.preimage continuous_subtype_val)
  · -- Each fiber of `f` is the finite union of the corresponding fibers on the pieces `s i`.
    have hfiber : f ⁻¹' {y} = ⋃ i, Subtype.val '' ((fun x : s i ↦ f x) ⁻¹' {y}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image,
        Subtype.exists]
      exact ⟨fun hfx ↦ let ⟨i, hxi⟩ := hmem x; ⟨i, x, hxi, hfx, rfl⟩,
        fun ⟨_, _, _, hfa, hax⟩ ↦ hax ▸ hfa⟩
    rw [hfiber]
    exact isCompact_iUnion fun i ↦
      ((hf i).isCompact_preimage isCompact_singleton).image continuous_subtype_val

/-- A map whose restrictions to the members of a finite closed cover are proper is proper. -/
theorem IsProperMap.of_iUnion_isClosed {ι : Type*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, IsClosed (s i)) (hcov : ⋃ i, s i = Set.univ)
    (hf : ∀ i, IsProperMap fun x : s i ↦ f x) : IsProperMap f :=
  (isProperMap_iff_iUnion_isClosed hs hcov).2 hf

/-- If two closed sets `s` and `t` cover `X`, then `f : X → Y` is proper if and only if its
restrictions to `s` and `t` are proper. -/
theorem isProperMap_iff_union_isClosed {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hcov : s ∪ t = Set.univ) :
    IsProperMap f ↔ (IsProperMap fun x : s ↦ f x) ∧ IsProperMap fun x : t ↦ f x := by
  refine (isProperMap_iff_iUnion_isClosed (s := fun b ↦ cond b s t) (Bool.forall_bool.2 ⟨ht, hs⟩)
    ?_).trans (Bool.forall_bool.trans and_comm)
  ext x
  simp [← hcov, or_comm]

/-- A map whose restrictions to two closed sets covering its domain are proper is proper. -/
theorem IsProperMap.of_union_isClosed {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hcov : s ∪ t = Set.univ) (hfs : IsProperMap fun x : s ↦ f x)
    (hft : IsProperMap fun x : t ↦ f x) : IsProperMap f :=
  (isProperMap_iff_union_isClosed hs ht hcov).2 ⟨hfs, hft⟩
