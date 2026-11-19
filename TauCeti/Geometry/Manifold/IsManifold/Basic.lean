/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Basic facts about manifolds, tangent spaces, and smoothness exponents

A smoothness exponent `n : ℕ∞ω` with `[ENat.LEInfty n]` is not `ω`, so it is the image of an
exponent in `ℕ∞`. Over a field satisfying `IsRCLikeNormedField`, `minSmoothness 𝕜 n = n`, so any
`Cⁿ` manifold is also a `C^(minSmoothness 𝕜 n)` manifold
(`IsManifold.minSmoothness_of_isRCLikeNormedField`). The tangent space `TangentSpace I x` of a
manifold modelled on `I : ModelWithCorners 𝕜 E H` is linearly equivalent to the model vector space
`E`, so its dimension is that of `E`. Tangent spaces at propositionally equal points are identified
by `tangentSpaceCast`.

## Main results

* `ENat.LEInfty.ne_top`: an exponent at most `∞` is not `ω`.
* `IsManifold.minSmoothness_of_isRCLikeNormedField`: a `Cⁿ` manifold over an `IsRCLikeNormedField`
  is a `C^(minSmoothness 𝕜 n)` manifold (opt-in local instance).
* `TauCeti.finrank_tangentSpace`: the tangent space at any point has the dimension of the model
  vector space.
* `TauCeti.heq_tangentSpaceCast`: over equal base points, `tangentSpaceCast` is heterogeneously
  the identity.
* `TauCeti.tangentSpaceCast_self`: identifying a tangent space with itself is the identity.
* `TauCeti.tangentSpaceCast_trans`: composing two `tangentSpaceCast` identifications across equal
  base points gives the direct identification.
* `TauCeti.eq_tangentSpaceCast_iff_tangentSpaceCast_eq`: tangent vectors over base points equal to
  a common point agree under direct transport if and only if they agree after transport to that
  common point.
-/

public section

open scoped ContDiff

/-- A smoothness exponent which is at most `∞` is not `ω`, the top element of `ℕ∞ω`. This is the
hypothesis needed to `lift` such an exponent to `ℕ∞`. -/
theorem ENat.LEInfty.ne_top (n : ℕ∞ω) [ENat.LEInfty n] : n ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top ENat.LEInfty.out

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Over a field satisfying `IsRCLikeNormedField`, `minSmoothness 𝕜 n = n`, so a `Cⁿ` manifold is a
`C^(minSmoothness 𝕜 n)` manifold. This theorem is deliberately not a global instance, so the
downgrade applies only in files that opt in with
`attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField`. -/
protected theorem IsManifold.minSmoothness_of_isRCLikeNormedField [IsRCLikeNormedField 𝕜] {n : ℕ∞ω}
    [IsManifold I n M] : IsManifold I (minSmoothness 𝕜 n) M := by
  rwa [_root_.minSmoothness_of_isRCLikeNormedField]

end Regularity

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

/-- Identifying a tangent space with itself via `tangentSpaceCast` is the identity. -/
@[simp]
theorem tangentSpaceCast_self {x : M} (w : TangentSpace I x) :
    tangentSpaceCast I x x w = w :=
  (rfl)

/-- Composing two `tangentSpaceCast` identifications across equal base points gives the direct
identification. -/
theorem tangentSpaceCast_trans {x y z : M} (hxy : x = y) (hyz : y = z) (w : TangentSpace I x) :
    tangentSpaceCast I y z (tangentSpaceCast I x y w) = tangentSpaceCast I x z w := by
  subst hxy; subst hyz
  rfl

/-- Two tangent vectors over base points equal to a common point `z` agree under direct transport
between their base points if and only if they agree after transport to `z`. -/
theorem eq_tangentSpaceCast_iff_tangentSpaceCast_eq {x y z : M} (hxz : x = z) (hyz : y = z)
    {u : TangentSpace I x} {v : TangentSpace I y} :
    u = tangentSpaceCast I y x v ↔ tangentSpaceCast I x z u = tangentSpaceCast I y z v := by
  subst hxz; subst hyz
  simp only [tangentSpaceCast_self]

end TauCeti
