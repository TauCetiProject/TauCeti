/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval

/-!
# Uniqueness of geodesic segments from initial data

Two geodesics on a preconnected parameter set agree if their position and velocity agree
at any one parameter, including an endpoint. The comparison takes place on the native
velocity lifts, so it also identifies their velocities without transporting tangent vectors
by hand. Only a C² metric on a C³ manifold is required for uniqueness.

For a smooth metric, a geodesic segment with prescribed initial data agrees with the
native maximal geodesic on any preconnected subset of its natural interval. This permits
results about the geodesic flow to be applied to geodesics presented as arbitrary curves.
The natural-domain inclusion remains explicit; no completeness assumption is used.

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
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) contMDiff_one_geodesicSpray heq

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

end FiniteRegularity

section Smooth

variable [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {p : M} {v : TangentSpace I p}

/-- A geodesic with initial data `(p, v)` agrees with the native maximal geodesic on a
preconnected parameter set contained in its natural domain, including closed intervals. -/
theorem IsGeodesicCurveOnFrom.eqOn_maximalGeodesic_of_subset
    (hγ : IsGeodesicCurveOnFrom I γ s p v) (hs : IsPreconnected s)
    (hsub : s ⊆ geodesicInterval I M p v) :
    EqOn (maximalGeodesic I M p v) γ s := by
  have hmax := (isGeodesicCurveOnFrom_maximalGeodesic (I := I) p v).mono
    hγ.isGeodesicCurveOn.uniqueDiffOn hsub hγ.zero_mem
  apply hmax.isGeodesicCurveOn.eqOn_of_curveVelocityLiftWithin_eq
    hγ.isGeodesicCurveOn hs hγ.zero_mem
  simpa only [curveVelocityLiftWithin_apply] using hmax.initial_eq.trans hγ.initial_eq.symm

end Smooth

end TauCeti.Manifold
