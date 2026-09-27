/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Compact Riemannian manifolds are geodesically complete

A Riemannian manifold carries no distance of its own: it carries the manifold topology and the
fibrewise inner products, and the Riemannian distance has to be installed from them. Installing the
*extended* distance `EMetricSpace.ofRiemannianMetric` turns a compact Riemannian manifold into a
compact extended metric space, hence into a complete one, and metric completeness gives geodesic
completeness. So every maximal geodesic of a compact Riemannian manifold is defined for all time,
and its exponential map is defined on the whole tangent space at every point.

Running the argument through the extended distance, which is available on any Riemannian manifold,
rather than through the ordinary distance, which exists only once the Riemannian distance is known
to be finite, keeps the conclusion free of any connectedness hypothesis. It therefore also covers a
compact manifold with several components, where points of different components are at infinite
Riemannian distance from each other.

Preconnectedness does enter the consequences drawn afterwards, which speak about the Riemannian
distance itself and so need it to be finite: on a compact preconnected Riemannian manifold every
point is the image `exp_p v` of a tangent vector whose norm is its distance to `p`, so `exp_p` is
surjective, and the radial geodesic segment along that vector realizes the distance.

## Main results

In the namespace `TauCeti.Manifold`:

* `isGeodesicallyCompleteAt_of_compactSpace`: **a compact Riemannian manifold is geodesically
  complete**, with `isGeodesicCurveOnFrom_maximalGeodesic_univ_of_compactSpace` the resulting
  all-time geodesics and `expDomain_eq_univ_of_compactSpace` the resulting everywhere-defined
  exponential map.
* `exists_riemannianExp_eq_and_enorm_eq_riemannianEDist_of_compactSpace` and
  `surjective_riemannianExp_of_compactSpace`: on a compact preconnected Riemannian manifold every
  point is reached from `p` by the exponential map, along a tangent vector whose norm is the
  Riemannian distance.
* `exists_isGeodesicCurveOn_Icc_pathELength_eq_riemannianEDist_of_compactSpace`: on a compact
  preconnected Riemannian manifold a minimizing geodesic segment joins `p` to every point.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Cor. 2.9.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space M] [T2Space (TangentBundle I M)] [CompactSpace M]

/-- **A compact Riemannian manifold is geodesically complete**: every maximal geodesic leaving a
point `p` is defined for all time. This is do Carmo's corollary to the Hopf–Rinow theorem. -/
theorem isGeodesicallyCompleteAt_of_compactSpace (p : M) : IsGeodesicallyCompleteAt I M p := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  -- The extended distance is available with no connectedness hypothesis, and a compact extended
  -- metric space is complete.
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  exact isGeodesicallyCompleteAt_of_completeSpace p

/-- **The exponential map of a compact Riemannian manifold is everywhere defined**, its domain
being the whole tangent space at every point. -/
@[simp]
theorem expDomain_eq_univ_of_compactSpace (p : M) : expDomain I M p = univ :=
  expDomain_eq_univ_iff.2 (isGeodesicallyCompleteAt_of_compactSpace p)

/-- In a compact Riemannian manifold the maximal geodesic with initial data `(p, v)` is a geodesic
on the whole real line. -/
theorem isGeodesicCurveOnFrom_maximalGeodesic_univ_of_compactSpace (p : M)
    (v : TangentSpace I p) :
    IsGeodesicCurveOnFrom I (maximalGeodesic I M p v) univ p v := by
  have hinterval : geodesicInterval I M p v = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, expDomain_eq_univ_of_compactSpace p, preimage_univ]
  have h := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  rwa [hinterval] at h

variable [PreconnectedSpace M]

/-- **Every point of a compact preconnected Riemannian manifold is reached minimally from `p` by
the exponential map**: it is `exp_p v` for a tangent vector `v` whose norm is the Riemannian
distance from `p` to it. -/
theorem exists_riemannianExp_eq_and_enorm_eq_riemannianEDist_of_compactSpace (p q : M) :
    ∃ v : TangentSpace I p, riemannianExp I M p v = q ∧ ‖v‖ₑ = riemannianEDist I p q := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hdomain : expDomain I M p = univ := expDomain_eq_univ_of_compactSpace p
  let : MetricSpace M := TauCeti.MetricSpace.ofRiemannianMetric I M
  obtain ⟨v, hv, hnorm⟩ := exists_riemannianExp_eq_and_norm_eq_dist hdomain q
  refine ⟨v, hv, ?_⟩
  rw [← ofReal_norm, hnorm, ← edist_dist, IsRiemannianManifold.out (I := I) p q]

/-- **The exponential map of a compact preconnected Riemannian manifold is surjective.** -/
theorem surjective_riemannianExp_of_compactSpace (p : M) :
    Surjective (riemannianExp I M p) := fun q ↦
  (exists_riemannianExp_eq_and_enorm_eq_riemannianEDist_of_compactSpace p q).imp fun _ h ↦ h.1

/-- **A minimizing geodesic segment joins `p` to every point of a compact preconnected Riemannian
manifold**: a geodesic on `[0, 1]` from `p` to `q` whose length is the Riemannian distance from `p`
to `q`, and each of whose subsegments likewise realizes the distance between its endpoints. -/
theorem exists_isGeodesicCurveOn_Icc_pathELength_eq_riemannianEDist_of_compactSpace (p q : M) :
    ∃ γ : ℝ → M, IsGeodesicCurveOn I γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
      pathELength I γ 0 1 = riemannianEDist I p q ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
        pathELength I γ s t = riemannianEDist I (γ s) (γ t) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hdomain : expDomain I M p = univ := expDomain_eq_univ_of_compactSpace p
  let : MetricSpace M := TauCeti.MetricSpace.ofRiemannianMetric I M
  obtain ⟨γ, hγ, h0, h1, hlength, hsub⟩ :=
    exists_isGeodesicCurveOn_Icc_pathELength_eq_edist hdomain q
  rw [IsRiemannianManifold.out (I := I) p q] at hlength
  refine ⟨γ, hγ, h0, h1, hlength, fun s hs t ht hst ↦ ?_⟩
  rw [← IsRiemannianManifold.out (I := I) (γ s) (γ t)]
  exact hsub s hs t ht hst

end TauCeti.Manifold

end
