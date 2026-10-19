/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Basic facts about tangent spaces

The tangent space `TangentSpace I x` of a manifold modelled on `I : ModelWithCorners 𝕜 E H` is
linearly equivalent to the model vector space `E`, so its dimension is that of `E`. Tangent spaces
at propositionally equal points are identified by `tangentSpaceCast`.

## Main results

* `TauCeti.finrank_tangentSpace`: the tangent space at any point has the dimension of the model
  vector space.
* `TauCeti.heq_tangentSpaceCast`: over equal base points, `tangentSpaceCast` is heterogeneously
  the identity.
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

/-- Over equal base points, `tangentSpaceCast` is heterogeneously the identity. This identifies
tangent vectors over base points that agree only propositionally, for instance when comparing
points of tangent bundles with `Bundle.TotalSpace.ext`. -/
theorem heq_tangentSpaceCast {x y : M} (hxy : x = y) (w : TangentSpace I x) :
    HEq (tangentSpaceCast I x y w) w := by
  subst hxy
  rfl

end TauCeti
