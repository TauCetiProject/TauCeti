/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Uniqueness

/-!
# Ambient geodesic uniqueness from actual endpoint velocity

On a boundaryless ambient manifold, equality of the actual endpoint tangent-bundle states
determines two geodesics on their common closed interval. The curves need only be differentiable
at the endpoint in addition to their genuine within-interval geodesic equations.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 3 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [I.Boundaryless]

/-- Equality of actual endpoint position and velocity determines ambient geodesics. -/
theorem IsGeodesicCurveOn.eqOn_Icc_of_curveVelocityLift_left_eq
    {γ δ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsGeodesicCurveOn I γ (Icc a b)) (hδ : IsGeodesicCurveOn I δ (Icc a b))
    (hγdiff : MDifferentiableAt 𝓘(ℝ) I γ a) (hδdiff : MDifferentiableAt 𝓘(ℝ) I δ a)
    (heq : curveVelocityLift I γ a = curveVelocityLift I δ a) : EqOn γ δ (Icc a b) := by
  apply hγ.eqOn_of_curveVelocityLiftWithin_eq hδ isPreconnected_Icc (left_mem_Icc.mpr hab.le)
  have hwithin {η : ℝ → M} (hη : MDifferentiableAt 𝓘(ℝ) I η a) :
      curveVelocityLiftWithin I η (Icc a b) a = curveVelocityLift I η a := by
    rw [curveVelocityLiftWithin_apply, curveVelocityLift_apply]
    congr 1
    rw [curveVelocityWithin_apply, curveVelocity_apply,
      mfderivWithin_eq_mfderiv
        ((uniqueDiffOn_Icc hab) a (left_mem_Icc.mpr hab.le)).uniqueMDiffWithinAt hη]
  rw [hwithin hγdiff, hwithin hδdiff]
  exact heq

end TauCeti.Manifold
