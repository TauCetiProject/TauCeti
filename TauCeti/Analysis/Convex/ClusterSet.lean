/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Topology.ClusterSet
import Mathlib.Analysis.Convex.PathConnected

/-!
# The cluster set of a map on a convex domain

In a real locally convex topological vector space, every point has a neighbourhood basis of convex
sets. Their intersections with a convex domain `U` are convex, hence preconnected. Thus a continuous
map on `U` with values in a compact Hausdorff set has a preconnected cluster set, by
`TauCeti.isPreconnected_clusterSetOn`.

The approach point `w` need not lie in `U`. At a point of `closure U`, compactness also makes the
cluster set nonempty, so it is connected; `TauCeti.isCompact_clusterSetOn` supplies its compactness.
No norm or separation assumption on the domain is needed.

For example, the unit disc, half-planes and convex polygons are convex. The cluster set of a bounded
holomorphic injection from the unit disc is therefore a continuum at each boundary point. This
is the connectedness input for Carathéodory's boundary correspondence, which proves that the
continuum is a singleton when the image is a Jordan domain.

## Main results

* `Convex.isPreconnected_clusterSetOn` and `Convex.isConnected_clusterSetOn`: on a convex domain
  the cluster set is preconnected, and is connected at a point of the closure.
* `Convex.isConnected_clusterSetOn_of_isBounded`: the form for a
  continuous map with bounded image into a proper metric space.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace Convex

open Set Topology TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

section Compact

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  {U : Set E} {K : Set Y} {f : E → Y} {w : E}

/-- A continuous map on a convex domain in a real locally convex space, with values in a compact
Hausdorff set, has a preconnected cluster set at every approach point. -/
theorem isPreconnected_clusterSetOn (hUc : Convex ℝ U) (hK : IsCompact K)
    (hfK : MapsTo f U K) (hfc : ContinuousOn f U) : IsPreconnected (clusterSetOn f U w) :=
  TauCeti.isPreconnected_clusterSetOn hK hfK hfc fun s hs => by
    obtain ⟨t, ⟨ht, htc⟩, hts⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) w).mem_iff.mp hs
    exact ⟨t, ht, hts, (hUc.inter htc).isPreconnected⟩

/-- A continuous map on a convex domain in a real locally convex space, with values in a compact
Hausdorff set, has a connected cluster set at each point of the closure of its domain.
Compactness of the cluster set is given by `TauCeti.isCompact_clusterSetOn`. -/
theorem isConnected_clusterSetOn (hUc : Convex ℝ U) (hK : IsCompact K)
    (hfK : MapsTo f U K) (hfc : ContinuousOn f U) (hw : w ∈ closure U) :
    IsConnected (clusterSetOn f U w) :=
  ⟨clusterSetOn_nonempty hK hfK hw, hUc.isPreconnected_clusterSetOn hK hfK hfc⟩

end Compact

section Proper

variable {Y : Type*} [MetricSpace Y] [ProperSpace Y]
  {U : Set E} {f : E → Y} {w : E}

/-- A continuous map on a convex domain in a real locally convex space, with bounded image in a
proper metric space, has a connected cluster set at each point of the closure of its domain.
Compactness of the cluster set is given by `TauCeti.isCompact_clusterSetOn_of_isBounded`. -/
theorem isConnected_clusterSetOn_of_isBounded (hUc : Convex ℝ U) (hfc : ContinuousOn f U)
    (hfb : Bornology.IsBounded (f '' U)) (hw : w ∈ closure U) :
    IsConnected (clusterSetOn f U w) :=
  hUc.isConnected_clusterSetOn hfb.isCompact_closure
    (fun z hz => subset_closure ⟨z, hz, rfl⟩) hfc hw

end Proper

end Convex
