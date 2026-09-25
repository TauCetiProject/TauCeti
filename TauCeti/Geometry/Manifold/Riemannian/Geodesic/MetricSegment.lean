/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
public import TauCeti.Topology.MetricSpace.Length
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Minimizing geodesics are metric geodesic segments

A metric geodesic segment from `x` to `y` is a curve on `[0, 1]` with
`dist (γ s) (γ t) = |s - t| * dist x y`, and a geodesic space is one in which every pair of points
is joined by such a segment. On a Riemannian manifold the segments are the minimizing radial
geodesics: if `v` is a tangent vector at `p` whose norm is the distance from `p` to `exp_p v`, the
maximal geodesic `t ↦ exp_p (t • v)` is a metric geodesic segment.

When `M` is complete the Hopf–Rinow theorem produces such a `v` for every pair of points, so a
complete Riemannian manifold is a geodesic space. That the manifold is a *length* space needs no
completeness; it is `TauCeti.Manifold.isLengthSpace`.

## Main results

In the namespace `TauCeti.Manifold`:

* `isGeodesicSegment_maximalGeodesic`: a geodesic whose initial velocity has the norm of the
  distance travelled is a metric geodesic segment.
* `exists_isGeodesicSegment_of_expDomain_eq_univ`: an everywhere-defined exponential map at `p`
  joins `p` to every point by a metric geodesic segment.
* `isGeodesicSpace_of_completeSpace`: **a complete Riemannian manifold is a geodesic space.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, assertion (f).
* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.5.
-/

public section

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

variable {p : M}

/-- **A minimizing geodesic is a metric geodesic segment.** Let `v` lie in the domain of `exp_p`
and satisfy `‖v‖ ≤ dist p (exp_p v)`, so that equality holds by `dist_riemannianExp_le`. Then the
maximal geodesic from `p` with initial velocity `v`, read on `[0, 1]`, is a geodesic segment from
`p` to `exp_p v` in the metric sense. -/
theorem isGeodesicSegment_maximalGeodesic {v : TangentSpace I p} (hv : v ∈ expDomain I M p)
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) :
    IsGeodesicSegment (maximalGeodesic I M p v) p (riemannianExp I M p v) where
  source := maximalGeodesic_zero p v
  target := (riemannianExp_def p v).symm
  dist_eq s hs t ht := by
    rw [← riemannianExp_smul p v s, ← riemannianExp_smul p v t,
      dist_riemannianExp_smul_riemannianExp_smul hv hmin hs ht,
      le_antisymm (dist_riemannianExp_le p v) hmin]

/-- **An everywhere-defined exponential map yields metric geodesic segments.** If `exp_p` is
defined on all of `T_p M`, every point `q` is joined to `p` by a metric geodesic segment. For the
segment as an explicit geodesic of the Riemannian connection, combine
`exists_riemannianExp_eq_and_norm_eq_dist` with `isGeodesicSegment_maximalGeodesic`. -/
theorem exists_isGeodesicSegment_of_expDomain_eq_univ (ha : expDomain I M p = univ) (q : M) :
    ∃ γ : ℝ → M, IsGeodesicSegment γ p q := by
  obtain ⟨v, hvq, hv⟩ := exists_riemannianExp_eq_and_norm_eq_dist ha q
  refine ⟨maximalGeodesic I M p v, ?_⟩
  rw [← hvq]
  exact isGeodesicSegment_maximalGeodesic (ha ▸ mem_univ v) (le_of_eq (by rw [hvq, hv]))

variable (I) in
include I in
/-- **A complete Riemannian manifold is a geodesic space**: any two of its points are joined by a
curve on `[0, 1]` that is parametrised proportionally to arclength and realises their distance.
The model `I` cannot be inferred from the conclusion, so it is an explicit argument. -/
theorem isGeodesicSpace_of_completeSpace [CompleteSpace M] : IsGeodesicSpace M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  exact ⟨fun x y ↦ exists_isGeodesicSegment_of_expDomain_eq_univ
    (expDomain_eq_univ_of_completeSpace (I := I) x) y⟩

end TauCeti.Manifold
