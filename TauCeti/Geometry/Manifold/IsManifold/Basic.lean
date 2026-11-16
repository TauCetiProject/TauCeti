/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Basic facts about tangent spaces and smoothness exponents

The tangent space `TangentSpace I x` of a manifold modelled on `I : ModelWithCorners 𝕜 E H` is
linearly equivalent to the model vector space `E`, so its dimension is that of `E`. Tangent spaces
at propositionally equal points are identified by `tangentSpaceCast`. A smoothness exponent
`n : ℕ∞ω` with `[ENat.LEInfty n]` is not `ω`, so it is the image of an exponent in `ℕ∞`.

## Main results

* `ENat.LEInfty.ne_top`: an exponent at most `∞` is not `ω`.
* `TauCeti.finrank_tangentSpace`: the tangent space at any point has the dimension of the model
  vector space.
* `TauCeti.heq_tangentSpaceCast`: over equal base points, `tangentSpaceCast` is heterogeneously
  the identity.
-/

public section

open scoped ContDiff

/-- A smoothness exponent which is at most `∞` is not `ω`, the top element of `ℕ∞ω`. This is the
hypothesis needed to `lift` such an exponent to `ℕ∞`. -/
theorem ENat.LEInfty.ne_top (n : ℕ∞ω) [ENat.LEInfty n] : n ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out

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
