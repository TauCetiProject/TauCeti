/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Regular

/-!
# Separation properties of disjoint unions

Mathlib proves that a disjoint union `Σ i, X i` of Hausdorff spaces is Hausdorff
(`Sigma.t2Space`). This file adds that a disjoint union of `T₁` spaces is `T₁`
(`Sigma.t1Space`), which Mathlib does not provide, that a disjoint union of regular spaces is
regular (`Sigma.regularSpace`), so that a disjoint union of `T₃` spaces is `T₃`, and that a
disjoint union of normal spaces is normal (`Sigma.normalSpace`). Each summand is an open and
closed subspace, so separating open or closed neighbourhoods constructed inside each summand stay
open or closed in the disjoint union.

Disjoint unions of disks are the spaces along which cells are attached to a cell complex, and
their regularity and normality are used to separate points and closed subsets across attached
cells.
-/

public section

open Set Topology

/-- A disjoint union of `T₁` spaces is `T₁`. -/
instance Sigma.t1Space {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T1Space (X i)] : T1Space (Σ i, X i) := by
  refine ⟨?_⟩
  rintro ⟨i, x⟩
  -- The singleton of a point of the disjoint union is the image of the corresponding singleton in
  -- its summand, which is closed in that summand; the inclusion of a summand is a closed map, so
  -- that image is closed in the disjoint union.
  rw [← Set.image_singleton]
  exact isClosedMap_sigmaMk (σ := X) (i := i) {x} (isClosed_singleton (x := x))

/-- A disjoint union of regular spaces is regular. -/
instance Sigma.regularSpace {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, RegularSpace (X i)] : RegularSpace (Σ i, X i) := by
  refine .of_exists_mem_nhds_isClosed_subset fun ⟨i, x⟩ s hs ↦ ?_
  rw [← IsOpenEmbedding.sigmaMk.map_nhds_eq] at hs
  obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hs
  exact ⟨Sigma.mk i '' t, IsOpenEmbedding.sigmaMk.map_nhds_eq x ▸ Filter.image_mem_map ht,
    isClosedMap_sigmaMk _ htc, Set.image_subset_iff.2 hts⟩

/-- A disjoint union of normal spaces is normal. -/
instance Sigma.normalSpace {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, NormalSpace (X i)] : NormalSpace (Σ i, X i) := by
  refine ⟨fun s t hs ht hst ↦ ?_⟩
  rw [isClosed_sigma_iff] at hs ht
  have hsep (i : ι) : ∃ u v : Set (X i), IsOpen u ∧ IsOpen v ∧
      Sigma.mk i ⁻¹' s ⊆ u ∧ Sigma.mk i ⁻¹' t ⊆ v ∧ Disjoint u v :=
    normal_separation (hs i) (ht i) (hst.preimage (Sigma.mk i))
  choose u v hu hv hsu htv huv using hsep
  refine ⟨⋃ i, Sigma.mk i '' u i, ⋃ i, Sigma.mk i '' v i,
    isOpen_iUnion fun i ↦ IsOpenEmbedding.sigmaMk.isOpenMap _ (hu i),
    isOpen_iUnion fun i ↦ IsOpenEmbedding.sigmaMk.isOpenMap _ (hv i),
    fun ⟨i, x⟩ hx ↦ mem_iUnion.2 ⟨i, x, hsu i hx, rfl⟩,
    fun ⟨i, x⟩ hx ↦ mem_iUnion.2 ⟨i, x, htv i hx, rfl⟩,
    disjoint_left.2 ?_⟩
  rintro _ hxu hxv
  obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.1 hxu
  obtain ⟨j, y, hy, heq⟩ := mem_iUnion.1 hxv
  cases heq
  exact (huv i).le_bot ⟨hx, hy⟩
