/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.IntegralCurve.Interval
import TauCeti.Topology.FiberBundle.Separation

/-!
# Uniqueness of geodesic segments from initial data

Two geodesics on a preconnected parameter set agree if their position and velocity agree
at any one parameter, including an endpoint. The comparison takes place on the native
velocity lifts, so it also identifies their velocities without transporting tangent vectors
by hand. Only a C² metric on a C³ manifold is required for uniqueness.
When both curves are differentiable at the initial parameter, equality of their actual
velocity lifts also suffices, including at the left endpoint of a closed interval.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4 and 10.
* The comparison uses `isMIntegralCurveOn_curveVelocityLiftWithin_iff` and the one-sided
  integral-curve uniqueness theorem `IsMIntegralCurveOn.eqOn_of_isPreconnected`.
-/

public noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section FiniteRegularity

variable [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {γ δ : ℝ → M} {s : Set ℝ} {a : ℝ}

/-- The position and velocity of a geodesic on a preconnected parameter set are determined
by its position and velocity at any one parameter, even an endpoint. -/
theorem IsGeodesicCurveOn.curveVelocityLiftWithin_eqOn
    (hγ : IsGeodesicCurveOn I γ s) (hδ : IsGeodesicCurveOn I δ s)
    (hs : IsPreconnected s) (ha : a ∈ s)
    (heq : curveVelocityLiftWithin I γ s a = curveVelocityLiftWithin I δ s a) :
    EqOn (curveVelocityLiftWithin I γ s) (curveVelocityLiftWithin I δ s) s := by
  have hγlift := (isMIntegralCurveOn_curveVelocityLiftWithin_iff
    hγ.uniqueDiffOn hγ.contMDiffOn).2 hγ
  have hδlift := (isMIntegralCurveOn_curveVelocityLiftWithin_iff
    hδ.uniqueDiffOn hδ.contMDiffOn).2 hδ
  exact hγlift.eqOn_of_isPreconnected hδlift hs ha
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint)
    (fun _ _ ↦ contMDiff_one_geodesicSpray.contMDiffAt) heq

/-- Geodesics with the same initial position and velocity agree on their preconnected
parameter set. The initial parameter may be an endpoint. -/
theorem IsGeodesicCurveOn.eqOn_of_curveVelocityLiftWithin_eq
    (hγ : IsGeodesicCurveOn I γ s) (hδ : IsGeodesicCurveOn I δ s)
    (hs : IsPreconnected s) (ha : a ∈ s)
    (heq : curveVelocityLiftWithin I γ s a = curveVelocityLiftWithin I δ s a) :
    EqOn γ δ s := by
  intro t ht
  simpa only [curveVelocityLiftWithin_proj] using
    congrArg TotalSpace.proj (hγ.curveVelocityLiftWithin_eqOn hδ hs ha heq ht)

/-- Geodesics on a preconnected parameter set agree when their actual position and velocity
agree at a parameter where both curves are differentiable, including an endpoint. -/
theorem IsGeodesicCurveOn.eqOn_of_curveVelocityLift_eq
    (hγ : IsGeodesicCurveOn I γ s) (hδ : IsGeodesicCurveOn I δ s)
    (hs : IsPreconnected s) (ha : a ∈ s)
    (hγdiff : MDifferentiableAt 𝓘(ℝ) I γ a) (hδdiff : MDifferentiableAt 𝓘(ℝ) I δ a)
    (heq : curveVelocityLift I γ a = curveVelocityLift I δ a) : EqOn γ δ s := by
  apply hγ.eqOn_of_curveVelocityLiftWithin_eq hδ hs ha
  have hwithin {η : ℝ → M} (hη : MDifferentiableAt 𝓘(ℝ) I η a) :
      curveVelocityLiftWithin I η s a = curveVelocityLift I η a := by
    rw [curveVelocityLiftWithin_apply, curveVelocityLift_apply]
    congr 1
    rw [curveVelocityWithin_apply, curveVelocity_apply,
      mfderivWithin_eq_mfderiv (hγ.uniqueDiffOn a ha).uniqueMDiffWithinAt hη]
  rw [hwithin hγdiff, hwithin hδdiff]
  exact heq

/-- Equality of actual endpoint position and velocity determines ambient geodesics. -/
theorem IsGeodesicCurveOn.eqOn_Icc_of_curveVelocityLift_left_eq
    {b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (Icc a b)) (hδ : IsGeodesicCurveOn I δ (Icc a b))
    (hγdiff : MDifferentiableAt 𝓘(ℝ) I γ a) (hδdiff : MDifferentiableAt 𝓘(ℝ) I δ a)
    (heq : curveVelocityLift I γ a = curveVelocityLift I δ a) : EqOn γ δ (Icc a b) := by
  by_cases hab : a ≤ b
  · exact hγ.eqOn_of_curveVelocityLift_eq hδ isPreconnected_Icc (left_mem_Icc.mpr hab)
      hγdiff hδdiff heq
  · simp only [Icc_eq_empty hab, eqOn_empty]

end FiniteRegularity

end TauCeti.Manifold
