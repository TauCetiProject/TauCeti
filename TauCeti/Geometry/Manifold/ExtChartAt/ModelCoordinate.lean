/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Extended charts at the model coordinate of a source point

For an open partial homeomorphism `e : OpenPartialHomeomorph M H` and a model with corners `I`,
the image of a point `x` of the source of `e` under the extended chart `e.extend I` is the model
coordinate `I (e x)`. Mathlib states the basic facts about `e.extend I` at `e.extend I x`; this file
states them at `I (e x)`, without unfolding `e.extend I x`:

* `OpenPartialHomeomorph.mem_extend_target`: `I (e x)` lies in the target of `e.extend I`;
* `OpenPartialHomeomorph.extend_symm_apply_of_mem_source`: the inverse extended chart sends
  `I (e x)` back to `x`;
* `OpenPartialHomeomorph.extend_target_mem_nhds`: for a boundaryless model, the target of
  `e.extend I` is a neighbourhood of `I (e x)`.

No smoothness or atlas assumption is involved.
-/

public section

open scoped Topology

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] {e : OpenPartialHomeomorph M H} {x : M}

/-- The model coordinate `I (e x)` of a point of the source of `e` lies in the target of the
extended chart. -/
theorem mem_extend_target (hx : x ∈ e.source) : I (e x) ∈ (e.extend I).target := by
  rw [e.extend_target']
  exact Set.mem_image_of_mem I (e.map_source hx)

/-- The inverse of the extended chart sends the model coordinate `I (e x)` of a point of the
source of `e` back to that point. -/
theorem extend_symm_apply_of_mem_source (hx : x ∈ e.source) :
    (e.extend I).symm (I (e x)) = x := by
  rw [e.extend_coe_symm, Function.comp_apply, I.left_inv, e.left_inv hx]

/-- For a boundaryless model, the target of the extended chart is a neighbourhood of the model
coordinate `I (e x)` of any point of the source of `e`. -/
theorem extend_target_mem_nhds [I.Boundaryless] (hx : x ∈ e.source) :
    (e.extend I).target ∈ 𝓝 (I (e x)) :=
  e.isOpen_extend_target.mem_nhds (e.mem_extend_target hx)

end OpenPartialHomeomorph
