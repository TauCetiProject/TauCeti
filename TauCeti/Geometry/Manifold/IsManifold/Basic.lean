/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Dimension of tangent spaces

The tangent space `TangentSpace I x` of a manifold modelled on `I : ModelWithCorners 𝕜 E H` is
linearly equivalent to the model vector space `E`, so its dimension is that of `E`.

## Main results

* `TauCeti.finrank_tangentSpace`: the tangent space at any point has the dimension of the model
  vector space.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent space at any point of a manifold has the dimension of the model vector space. -/
@[simp]
theorem finrank_tangentSpace (x : M) : Module.finrank 𝕜 (TangentSpace I x) = Module.finrank 𝕜 E :=
  (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq

end TauCeti
