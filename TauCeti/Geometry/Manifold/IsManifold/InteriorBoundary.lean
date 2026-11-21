/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Interior points of a model space

A model space `H`, charted over itself, has the identity as its preferred chart. So a point of `H`
is an interior point for a model with corners `I` exactly when `I` sends it into the interior of
its range (`ModelWithCorners.isInteriorPoint_iff_mem_interior_range_self`).
-/

public section

open Set

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

/-- On a model space, a point is an interior point exactly when the model sends it into the
interior of its range. -/
theorem isInteriorPoint_iff_mem_interior_range_self {z : H} :
    I.IsInteriorPoint z ↔ I z ∈ interior (range I) := by
  rw [IsInteriorPoint, extChartAt_self_apply]

end ModelWithCorners
