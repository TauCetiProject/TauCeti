/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.MetricSpace.Length

/-!
# Geodesic segments as points of path space

The path space of a topological space `X` is `C(I, X)`, the continuous maps from the unit interval
with the compact-open topology; when `X` is a pseudometric space, as below, this is the topology of
uniform convergence since the domain is compact.
This file singles out the geodesic segments inside it: `TauCeti.geodesicPaths X` is the set of
paths `γ` with `dist (γ s) (γ t) = |s - t| * dist (γ 0) (γ 1)`. These are exactly the restrictions
to `[0, 1]` of the curves `TauCeti.IsGeodesicSegment` describes, so a pseudometric space is a
geodesic space exactly when every pair of points is the pair of endpoints of a geodesic path.

The defining identity only involves finitely many evaluations at a time, so the set of geodesic
paths is closed in path space, and on a metric space so is the relation between a pair of points
and a geodesic path joining them. On a Polish space this relation is therefore a closed subset of
a Polish space; this is the input that a measurable selection theorem needs to choose a geodesic
measurably in its endpoints, which is how a law of pairs of points is lifted to a law of geodesics
in optimal transport.

## Main definitions

* `TauCeti.geodesicPaths X`: the geodesic segments of `X`, as a subset of `C(I, X)`.

## Main results

* `TauCeti.mem_geodesicPaths_iff_isGeodesicSegment`: a path is a geodesic path exactly when its
  extension to `ℝ` is a geodesic segment between its endpoints.
* `TauCeti.exists_mem_geodesicPaths_iff`: two points are the endpoints of a geodesic path exactly
  when they are joined by a geodesic segment; `TauCeti.isGeodesicSpace_iff_exists_mem_geodesicPaths`
  restates the geodesic-space condition this way.
* `TauCeti.isClosed_geodesicPaths`: the geodesic paths form a closed subset of path space.
* `TauCeti.isClosed_setOf_mem_geodesicPaths_endpoints`: on a metric space, the relation between a
  pair of points and the geodesic paths joining them is closed.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §2.1 and §7.2.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 7.
-/

public section

open Set
open scoped unitInterval

namespace TauCeti

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X] {γ : C(I, X)} {x y : X}

variable (X) in
/-- The *geodesic paths* of `X`: the continuous paths `γ : C(I, X)` with
`dist (γ s) (γ t) = |s - t| * dist (γ 0) (γ 1)` for all times `s` and `t`. These are the geodesic
segments from `γ 0` to `γ 1`, parametrised proportionally to arclength, viewed as points of path
space. -/
def geodesicPaths : Set C(I, X) :=
  {γ | ∀ s t : I, dist (γ s) (γ t) = |(s : ℝ) - t| * dist (γ 0) (γ 1)}

/-- Membership in the geodesic paths, unfolded. -/
@[simp]
theorem mem_geodesicPaths_iff :
    γ ∈ geodesicPaths X ↔ ∀ s t : I, dist (γ s) (γ t) = |(s : ℝ) - t| * dist (γ 0) (γ 1) :=
  Iff.rfl

/-- A path is a geodesic path exactly when its extension to `ℝ`, constant outside `[0, 1]`, is a
geodesic segment between its endpoints. -/
theorem mem_geodesicPaths_iff_isGeodesicSegment :
    γ ∈ geodesicPaths X ↔ IsGeodesicSegment (IccExtend zero_le_one γ) (γ 0) (γ 1) := by
  refine ⟨fun h ↦ ⟨IccExtend_left .., IccExtend_right .., fun s hs t ht ↦ ?_⟩, fun h s t ↦ ?_⟩
  · simpa only [IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ ht] using h ⟨s, hs⟩ ⟨t, ht⟩
  · simpa only [IccExtend_val] using h.dist_eq s s.2 t t.2

/-- The restriction to `[0, 1]` of a geodesic segment is a geodesic path. -/
theorem IsGeodesicSegment.restrict_mem_geodesicPaths {γ : ℝ → X} (h : IsGeodesicSegment γ x y) :
    (⟨(Icc 0 1).domRestrict γ, h.continuousOn.domRestrict⟩ : C(I, X)) ∈ geodesicPaths X := by
  intro s t
  have h0 : γ ((0 : I) : ℝ) = x := h.source
  have h1 : γ ((1 : I) : ℝ) = y := h.target
  simp only [ContinuousMap.coe_mk, domRestrict_apply, h0, h1]
  exact h.dist_eq s s.2 t t.2

/-- Two points are the endpoints of a geodesic path exactly when they are joined by a geodesic
segment. -/
theorem exists_mem_geodesicPaths_iff :
    (∃ γ ∈ geodesicPaths X, γ 0 = x ∧ γ 1 = y) ↔ ∃ γ : ℝ → X, IsGeodesicSegment γ x y := by
  refine ⟨?_, fun ⟨γ, hγ⟩ ↦ ⟨_, hγ.restrict_mem_geodesicPaths, hγ.source, hγ.target⟩⟩
  rintro ⟨γ, hγ, rfl, rfl⟩
  exact ⟨_, mem_geodesicPaths_iff_isGeodesicSegment.1 hγ⟩

/-- A pseudometric space is a geodesic space exactly when every pair of points is the pair of
endpoints of a geodesic path. -/
theorem isGeodesicSpace_iff_exists_mem_geodesicPaths :
    IsGeodesicSpace X ↔ ∀ x y : X, ∃ γ ∈ geodesicPaths X, γ 0 = x ∧ γ 1 = y := by
  simp only [exists_mem_geodesicPaths_iff]
  exact ⟨fun h ↦ h.exists_isGeodesicSegment, fun h ↦ ⟨h⟩⟩

/-- In a geodesic space, any two points are the endpoints of a geodesic path. -/
theorem IsGeodesicSpace.exists_mem_geodesicPaths [IsGeodesicSpace X] (x y : X) :
    ∃ γ ∈ geodesicPaths X, γ 0 = x ∧ γ 1 = y :=
  isGeodesicSpace_iff_exists_mem_geodesicPaths.1 ‹_› x y

/-- The geodesic paths form a closed subset of path space. -/
theorem isClosed_geodesicPaths : IsClosed (geodesicPaths X) := by
  simp only [geodesicPaths, ofPred_forall]
  exact isClosed_iInter fun s ↦ isClosed_iInter fun t ↦ isClosed_eq (by fun_prop) (by fun_prop)

end PseudoMetric

section Metric

variable {X : Type*} [MetricSpace X]

/-- The relation between a pair of points of a metric space and the geodesic paths joining them is
closed in `(X × X) × C(I, X)`. -/
theorem isClosed_setOf_mem_geodesicPaths_endpoints :
    IsClosed {q : (X × X) × C(I, X) | q.2 ∈ geodesicPaths X ∧ (q.2 0, q.2 1) = q.1} :=
  (isClosed_geodesicPaths.preimage continuous_snd).inter (isClosed_eq (by fun_prop) (by fun_prop))

end Metric

end TauCeti
