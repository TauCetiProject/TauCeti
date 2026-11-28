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

* `OpenPartialHomeomorph.extend_symm_mem_source`: `(e.extend I).symm y ∈ e.source` for
  `y ∈ (e.extend I).target`.
* `ModelWithCorners.extend_mem_extendCoordChange_source` and
  `ModelWithCorners.mem_extendCoordChange_source`: membership in `(I.extendCoordChange e e').source`
  from overlap membership in `M` or in `(e.extend I).target`.
* `ModelWithCorners.extendCoordChange_extend_apply`,
  `ModelWithCorners.extendCoordChange_apply_eq`, and
  `ModelWithCorners.extend_symm_extendCoordChange`: evaluating `I.extendCoordChange e e'` without
  unfolding its definition.
-/

public section

open scoped Manifold Topology

section CoordChange

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]

/-- The inverse of an extended chart sends a point of its target into the source of the
underlying chart. -/
theorem OpenPartialHomeomorph.extend_symm_mem_source {e : OpenPartialHomeomorph M H} {y : E}
    (hy : y ∈ (e.extend I).target) : (e.extend I).symm y ∈ e.source := by
  simpa only [← e.extend_source (I := I)] using (e.extend I).map_target hy

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
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact ⟨(e.extend I).symm y, ⟨e.extend_symm_mem_source hy, hy'⟩, (e.extend I).right_inv hy⟩

/-- Evaluating an extended coordinate change at `e.extend I x` yields `e'.extend I x` when
`x ∈ e.source`. -/
theorem ModelWithCorners.extendCoordChange_extend_apply {e e' : OpenPartialHomeomorph M H}
    {x : M} (hx : x ∈ e.source) :
    I.extendCoordChange e e' (e.extend I x) = e'.extend I x := by
  rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
    (e.extend I).left_inv (e.extend_source (I := I) ▸ hx)]

/-- Evaluating an extended coordinate change at `y` applies `e'.extend I` to
`(e.extend I).symm y`. -/
theorem ModelWithCorners.extendCoordChange_apply_eq (e e' : OpenPartialHomeomorph M H) (y : E) :
    I.extendCoordChange e e' y = e'.extend I ((e.extend I).symm y) :=
  PartialEquiv.trans_apply (e.extend I).symm (e'.extend I)

/-- Applying `(e'.extend I).symm` after `I.extendCoordChange e e'` on its source recovers
`(e.extend I).symm`. -/
theorem ModelWithCorners.extend_symm_extendCoordChange {e e' : OpenPartialHomeomorph M H}
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    (e'.extend I).symm (I.extendCoordChange e e' y) = (e.extend I).symm y := by
  rw [I.extendCoordChange_apply_eq]
  exact (e'.extend I).left_inv hy.2

end CoordChange
