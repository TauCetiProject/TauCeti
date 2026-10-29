/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper maps: composition with homeomorphisms and products

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

* `Homeomorph.comp_isProperMap_iff` and `Homeomorph.comp_isProperMap_iff'`: properness is
  invariant under composition with a homeomorphism.
* `IsProperMap.of_prodMap_left` and `IsProperMap.of_prodMap_right`: the factors of a proper
  product map with nonempty sources are proper.
* `isProperMap_prodMap_iff`: for nonempty sources, `Prod.map f g` is proper exactly when `f` and
  `g` are.
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
