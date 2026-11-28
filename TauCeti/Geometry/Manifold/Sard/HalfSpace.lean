/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sard.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Geometry.Manifold.Corners.Depth
import TauCeti.Geometry.Manifold.Sard.Corners

/-!
# Sard's theorem for manifolds with boundary

For a map from a Lindelöf manifold modelled on the Euclidean half-space, the critical values
are chartwise null, and the regular values are dense. The target may have corners and its
model may have any finite dimension. The regularity bound is the sharp Sard bound
`k > dim M - dim N`, with `k ≥ 1`; in particular smooth maps satisfy it.

Since `range (𝓡∂ d)` is cut out in `EuclideanSpace ℝ (Fin d)` by the single coordinate
inequality `0 ≤ z 0` (`ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq`),
a manifold with boundary modelled on `𝓡∂ d` is a special case of a manifold with corners
modelled on a coordinate-nonnegative cone (whose two strata are the interior of dimension `d`
and the boundary of dimension `d - 1`). All three results here follow directly from
`TauCeti.isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv` and its corollaries in
`TauCeti.Geometry.Manifold.Sard.Corners`, where at any critical point the restriction to its
stratum is also critical (`TauCeti.IsRegularPoint.of_comp`). The converse implication on
critical points is false: the identity on the half-line is regular at its endpoint, while its
restriction to that endpoint is critical.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_halfSpace`: a pointwise version for any set
  of critical points.
* `ContMDiff.isNullSet_image_criticalPoints_halfSpace`: the critical values are null.
* `ContMDiff.dense_isRegularValue_halfSpace`: the regular values are dense.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 6.10, including the reduction from manifolds with boundary to their interior and
  boundary.
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {d : ℕ} [NeZero d] {k : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
  [IsManifold (𝓡∂ d) k M] [LindelofSpace M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J k N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary**, on a set of critical points. Let `M` be a
Lindelöf half-space `C^k` manifold of dimension `d` and `N` a finite-dimensional real `C^k`
manifold. If `f` is `C^k` at every point of a set `s` of critical points, then `f '' s` is null
when `k > d - dim N` and `k ≥ 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ d) J k f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ d) J f x) : IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv (EuclideanSpace.equiv (Fin d) ℝ)
    (ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq d)
    (by simpa [finrank_euclideanSpace_fin] using hk) hf hs

/-- The critical values of a `C^k` map from a Lindelöf half-space `C^k` manifold of dimension
`d` to a finite-dimensional real `C^k` manifold `N` are null when `k > d - dim N` and `k ≥ 1`.
In particular, this holds for every smooth map. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace
    (hf : ContMDiff (𝓡∂ d) J k f)
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ d) J f x}) :=
  hf.isNullSet_image_criticalPoints_of_range_eq_equiv (EuclideanSpace.equiv (Fin d) ℝ)
    (ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq d)
    (by simpa [finrank_euclideanSpace_fin] using hk)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The regular values of a `C^k` map from a Lindelöf half-space `C^k` manifold of dimension
`d` to a finite-dimensional real `C^k` manifold `N` are dense when `k > d - dim N` and `k ≥ 1`.
In particular, this holds for every smooth map. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace
    (hf : ContMDiff (𝓡∂ d) J k f)
    (hk : ((d - finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ k) :
    Dense {y | IsRegularValue (𝓡∂ d) J f y} :=
  hf.dense_isRegularValue_of_range_eq_equiv (EuclideanSpace.equiv (Fin d) ℝ)
    (ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq d)
    (by simpa [finrank_euclideanSpace_fin] using hk)

end TauCeti
