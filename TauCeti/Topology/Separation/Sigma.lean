/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Regular

/-!
# Regularity of disjoint unions

Mathlib proves that a disjoint union `Σ i, X i` of Hausdorff spaces is Hausdorff
(`Sigma.t2Space`). This file adds that a disjoint union of `T₁` spaces is `T₁`
(`Sigma.t1Space`), which Mathlib does not provide, and that a disjoint union of regular spaces is
regular (`Sigma.regularSpace`), so that a disjoint union of `T₃` spaces is `T₃`. Each summand is
an open and closed subspace, so a closed neighbourhood of a point inside its summand is a closed
neighbourhood in the disjoint union.

Disjoint unions of disks are the spaces along which cells are attached to a cell complex, and
their regularity is used to separate a point of an open cell from the rest of the complex.
-/

public section

open Topology

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
