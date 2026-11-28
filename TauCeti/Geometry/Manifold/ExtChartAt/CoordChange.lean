/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Domain membership and evaluation for extended coordinate changes

This file collects basic membership and evaluation lemmas for extended charts `e.extend I` and
extended coordinate changes `I.extendCoordChange e e'`, without smoothness or measure-theoretic
assumptions.

## Main results

* `ModelWithCorners.extend_mem_extendCoordChange_source` and
  `ModelWithCorners.mem_extendCoordChange_source`: membership in `(I.extendCoordChange e e').source`
  from overlap membership in `M` or in `(e.extend I).target`.
* `ModelWithCorners.extend_symm_extendCoordChange`: cancelling `(e'.extend I).symm` after
  `I.extendCoordChange e e'` on its source.
-/

public section

open scoped Manifold Topology

section CoordChange

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]

/-- The image in `e.extend I` of a point in the overlap `e.source ∩ e'.source` belongs to the
source of `I.extendCoordChange e e'`. -/
theorem ModelWithCorners.extend_mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    e.extend I x ∈ (I.extendCoordChange e e').source := by
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact Set.mem_image_of_mem _ ⟨hx, hx'⟩

/-- A point in `(e.extend I).target` whose inverse chart image belongs to `e'.source` lies in
the source of `I.extendCoordChange e e'`. -/
theorem ModelWithCorners.mem_extendCoordChange_source {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (e.extend I).target) (hy' : (e.extend I).symm y ∈ e'.source) :
    y ∈ (I.extendCoordChange e e').source := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
    e'.extend_source]
  exact ⟨hy, hy'⟩

/-- Applying `(e'.extend I).symm` after `I.extendCoordChange e e'` on its source recovers
`(e.extend I).symm`. -/
theorem ModelWithCorners.extend_symm_extendCoordChange {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    (e'.extend I).symm (I.extendCoordChange e e' y) = (e.extend I).symm y := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
  exact (e'.extend I).left_inv hy.2

end CoordChange
