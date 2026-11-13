/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

/-!
# Relative volume density on open submanifolds

Restricting both Riemannian metrics to an open submanifold preserves their relative volume
density. The canonical tangent-space identification transports a basis and preserves both
Gram matrices.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

/-- Restricting both metrics to an open submanifold preserves their relative volume density. -/
@[simp]
theorem relativeVolumeDensity_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (U : TopologicalSpace.Opens M) (x : U) :
    relativeVolumeDensity (g.restrictOpenTangentSpace U) (g'.restrictOpenTangentSpace U) x =
      relativeVolumeDensity g g' x.val := by
  let b := Module.finBasis ℝ (TangentSpace I x)
  let e := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv
  rw [b.relativeVolumeDensity_eq_sqrt_div, (b.map e).relativeVolumeDensity_eq_sqrt_div]
  simp only [e, restrictOpenTangentSpace_inner, Module.Basis.map_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv]

end Bundle.ContMDiffRiemannianMetric
