/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Extended charts after restriction of scalars

Restricting the scalars of a boundaryless model leaves its coordinate maps unchanged.
Consequently its extended charts are unchanged as partial equivalences. This comparison
allows differentiability and smoothness arguments in these coordinates to use scalar
restriction without replacing the charted space, including for product and recharted models.

For underlying real manifolds, see Huybrechts, *Complex Geometry*, Chapter 1.
-/

public section

open scoped Manifold

namespace ModelWithCorners

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

variable (𝕜)

/-- Scalar restriction leaves the extended chart unchanged, including its source, target,
and inverse. No compatibility between the two scalar actions is needed for this equality. -/
-- extChartAt itself unfolds under simp; this equality is for rewriting while keeping charts folded.
theorem extChartAt_restrictScalars (I : ModelWithCorners 𝕜' E H) [I.Boundaryless]
    (x : M) : extChartAt (I.restrictScalars 𝕜) x = extChartAt I x := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, restrictScalars_toPartialEquiv]

end ModelWithCorners
