/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic

/-!
# The complete hyperbolic metric on upper half-space

Package the standard metric `(‖dx‖² + dt²) / t²` with its proved completeness and
constant-curvature tensor as a `HyperbolicMetric`. This gives an explicit metric witness
for hyperbolic space in every positive dimension, usable by the hyperbolic volume API.
The underlying Riemannian metric is exactly the previously installed upper-half-space metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (hyperbolic space in the upper-half-space model).
-/

public section

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, P)

/-- The standard complete metric of constant curvature `-1` on upper half-space. -/
def hyperbolicMetric : HyperbolicMetric (I := J) (M := UpperHalfSpace E) where
  metric := { riemannianMetric with contMDiff := riemannianMetric.contMDiff.of_le le_top }
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact curvatureTensor_eq

/-- Forgetting completeness and curvature recovers the standard upper-half-space metric. -/
@[simp] theorem hyperbolicMetric_toRiemannianMetric :
    (hyperbolicMetric (E := E)).metric.toRiemannianMetric = riemannianMetric.toRiemannianMetric :=
  (rfl)

/-- Upper half-space with its standard manifold structure admits a complete hyperbolic metric. -/
theorem isHyperbolic : IsHyperbolic (I := J) (M := UpperHalfSpace E) :=
  TauCeti.isHyperbolic_iff.mpr ⟨hyperbolicMetric⟩

end TauCeti.UpperHalfSpace
