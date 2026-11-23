/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Compactness.Compact

/-!
# Compact exhaustions

This file provides general constructions and lemmas for `CompactExhaustion`:

* `IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`: a sigma-compact
  open subset of a locally compact space has a monotone sequence of compact subsets exhausting it.
* `CompactExhaustion.union`: pointwise union of two compact exhaustions.
* `CompactExhaustion.unionImage`: enlarging a compact exhaustion by the images of a compact
  exhaustion along a continuous open map.
* `CompactExhaustion.preimage`: pulling back a compact exhaustion along a proper map.
* `CompactExhaustion.closure_image_subset_range`: in a Hausdorff codomain, the closure of the image
  of each stage of a compact exhaustion lies in the range of a continuous map.
* `CompactExhaustion.subtype` and `TauCeti.isOpen_of_subset_interior_succ`: conversely, compact
  subsets `Kₙ ⊆ U` of the ambient space with `Kₙ ⊆ interior Kₙ₊₁` that cover a subset `U` trace
  a compact exhaustion of the subspace `U`, and such a `U` is open.
-/

public section

open Set

/-- A sigma-compact open subset `Ω` of a locally compact space has a monotone sequence of
compact subsets of `Ω` such that every compact subset of `Ω` lies in one of them. -/
theorem IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {Ω : Set X} [SigmaCompactSpace Ω] (hΩ : IsOpen Ω) :
    ∃ L : ℕ → Set X, (∀ m, IsCompact (L m)) ∧ (∀ m, L m ⊆ Ω) ∧ Monotone L ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ m, K ⊆ L m := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let Kx : CompactExhaustion Ω := CompactExhaustion.choice Ω
  refine ⟨fun m => (↑) '' Kx m, fun m => (Kx.isCompact m).image continuous_subtypeVal,
    fun m => ?_, fun m m' h => image_mono (Kx.subset h), fun K hK hKΩ => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.property
  · have hK' : IsCompact (((↑) : Ω → X) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
    obtain ⟨m, hm⟩ := Kx.exists_superset_of_isCompact hK'
    exact ⟨m, fun x hx => ⟨⟨x, hKΩ hx⟩, hm hx, rfl⟩⟩

namespace TauCeti

/-- A subset `U` covered by subsets `Kₙ ⊆ U` with `Kₙ ⊆ interior Kₙ₊₁` is open: it is the union of
the interiors of the `Kₙ`. -/
theorem isOpen_of_subset_interior_succ {X : Type*} [TopologicalSpace X] {U : Set X}
    {K : ℕ → Set X} (hKU : ∀ n, K n ⊆ U) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
    (hcover : U ⊆ ⋃ n, K n) : IsOpen U := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hx)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hsub n hn)) (hKU (n + 1))

end TauCeti

namespace CompactExhaustion

/-- The pointwise union of two compact exhaustions is a compact exhaustion. -/
def union {X : Type*} [TopologicalSpace X] (K K' : CompactExhaustion X) :
    CompactExhaustion X where
  toFun n := K n ∪ K' n
  isCompact' n := (K.isCompact n).union (K'.isCompact n)
  subset_interior_succ' n :=
    Set.union_subset
      ((K.subset_interior_succ n).trans (interior_mono Set.subset_union_left))
      ((K'.subset_interior_succ n).trans (interior_mono Set.subset_union_right))
  iUnion_eq' := by
    rw [Set.iUnion_union_distrib, K.iUnion_eq, Set.univ_union]

@[simp]
lemma union_apply {X : Type*} [TopologicalSpace X] (K K' : CompactExhaustion X) (n : ℕ) :
    (K.union K') n = K n ∪ K' n :=
  (rfl)

/-- Enlarging a compact exhaustion of `V` by the images of a compact exhaustion of `W` along a
continuous open map `i : W → V` yields a compact exhaustion of `V`. -/
def unionImage {W V : Type*} [TopologicalSpace W] [TopologicalSpace V]
    (K : CompactExhaustion V) (L : CompactExhaustion W) {i : W → V}
    (hi_cont : Continuous i) (hi_open : IsOpenMap i) : CompactExhaustion V where
  toFun n := K n ∪ i '' L n
  isCompact' n := (K.isCompact n).union ((L.isCompact n).image hi_cont)
  subset_interior_succ' n := by
    refine Set.union_subset
      ((K.subset_interior_succ n).trans (interior_mono Set.subset_union_left)) ?_
    calc i '' L n ⊆ i '' interior (L (n + 1)) := Set.image_mono (L.subset_interior_succ n)
      _ ⊆ interior (i '' L (n + 1)) := hi_open.image_interior_subset _
      _ ⊆ interior (K (n + 1) ∪ i '' L (n + 1)) := interior_mono Set.subset_union_right
  iUnion_eq' := by
    rw [Set.iUnion_union_distrib, K.iUnion_eq, Set.univ_union]

@[simp]
lemma unionImage_apply {W V : Type*} [TopologicalSpace W] [TopologicalSpace V]
    (K : CompactExhaustion V) (L : CompactExhaustion W) {i : W → V}
    (hi_cont : Continuous i) (hi_open : IsOpenMap i) (n : ℕ) :
    (K.unionImage L hi_cont hi_open) n = K n ∪ i '' L n :=
  (rfl)

/-- Pulling back a compact exhaustion along a proper continuous map yields a compact exhaustion. -/
def preimage {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (K : CompactExhaustion V) {f : U → V} (hf : IsProperMap f) : CompactExhaustion U where
  toFun n := f ⁻¹' K n
  isCompact' n := hf.isCompact_preimage (K.isCompact n)
  subset_interior_succ' n :=
    (Set.preimage_mono (K.subset_interior_succ n)).trans
      (preimage_interior_subset_interior_preimage hf.continuous)
  iUnion_eq' := by
    rw [← Set.preimage_iUnion, K.iUnion_eq, Set.preimage_univ]

@[simp]
lemma preimage_apply {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (K : CompactExhaustion V) {f : U → V} (hf : IsProperMap f) (n : ℕ) :
    K.preimage hf n = f ⁻¹' K n :=
  (rfl)

/-- In a Hausdorff codomain, the closure of the image of every stage of a compact exhaustion lies
in the range of a continuous map. -/
theorem closure_image_subset_range {V X : Type*} [TopologicalSpace V] [TopologicalSpace X]
    [T2Space X] (K : CompactExhaustion V) {f : V → X} (hf : Continuous f) (n : ℕ) :
    closure (f '' K n) ⊆ Set.range f :=
  (K.isCompact n).closure_image_subset_range hf.continuousOn

section Subtype

variable {X : Type*} [TopologicalSpace X] (U : Set X) (K : ℕ → Set X)
  (hK : ∀ n, IsCompact (K n)) (hKU : ∀ n, K n ⊆ U) (hsub : ∀ n, K n ⊆ interior (K (n + 1)))
  (hcover : U ⊆ ⋃ n, K n)

/-- Compact subsets `Kₙ ⊆ U` of the ambient space with `Kₙ ⊆ interior Kₙ₊₁` that cover `U` trace
the compact exhaustion `n ↦ U ∩ Kₙ` of the subspace `U`. -/
-- The body is exposed so that its sets unfold to the preimages `Subtype.val ⁻¹' Kₙ`: pairs and
-- chain complexes built from the exhaustion must agree with those built from these preimages up to
-- definitional equality, as in the twisted relative chains of `U` and of `X`.
@[expose]
def subtype : CompactExhaustion U where
  toFun n := Subtype.val ⁻¹' K n
  isCompact' n := Subtype.isCompact_iff.2 <| by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 (hKU n)]
    exact hK n
  subset_interior_succ' n := (preimage_mono (hsub n)).trans
    (preimage_interior_subset_interior_preimage continuous_subtypeVal)
  iUnion_eq' := eq_univ_of_forall fun x ↦ by simpa using hcover x.property

@[simp]
theorem subtype_apply (n : ℕ) :
    CompactExhaustion.subtype U K hK hKU hsub hcover n = Subtype.val ⁻¹' K n :=
  (rfl)

end Subtype

end CompactExhaustion
