/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Basic
public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra

import TauCeti.Topology.Algebra.Group.Separation

/-!
# Countable subgroups

A countable subgroup with a connected immersed Lie-subgroup presentation is trivial.
In a finite dimensional real Lie group, every countable subgroup has zero canonical Lie
algebra, including subgroups that are not closed. The two immersed-subgroup criteria also
hold for arbitrary ambient normed models.

Countable subsets of T35 spaces are totally disconnected. Topological groups are completely
regular and Lie groups are Hausdorff, so connected subsets of countable subgroups are singletons.
In particular, every exponential curve contained in a countable subgroup is constant.

## Main results

* `TauCeti.Lie.ImmersedLieSubgroupData.eq_bot_of_countable`: a countable image of a connected
  immersed presentation is trivial.
* `TauCeti.Lie.IsImmersedLieSubgroup.eq_bot_of_countable`: a countable immersed subgroup is trivial.
* `TauCeti.Lie.lieSubalgebraOfSubgroup_eq_bot_of_countable`: a countable subgroup has zero
  canonical Lie algebra.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 7,
  Proposition 7.17, pp.157–158, for intrinsic immersed subgroup presentations.
* Mathlib, `Topology/Separation/CompletelyRegular.lean`, for total disconnectedness of
  countable subsets.
-/

public section

open Set Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie


variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
/-- A countable subgroup admitting a connected immersed presentation is trivial. -/
theorem ImmersedLieSubgroupData.eq_bot_of_countable {K : Subgroup G}
    (d : TauCeti.Lie.ImmersedLieSubgroupData I K) (hK : (K : Set G).Countable) : K = ⊥ := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact d.eq_bot_of_isTotallyDisconnected hK.isTotallyDisconnected

/-- A countable immersed Lie subgroup is trivial. -/
theorem IsImmersedLieSubgroup.eq_bot_of_countable {K : Subgroup G}
    (h : IsImmersedLieSubgroup (I := I) K) (hK : (K : Set G).Countable) : K = ⊥ := by
  obtain ⟨d⟩ := isImmersedLieSubgroup_iff.mp h
  exact d.eq_bot_of_countable hK

variable [FiniteDimensional ℝ E] [T2Space G]

/-- The canonical Lie algebra of any countable subgroup is zero, without closedness. -/
theorem lieSubalgebraOfSubgroup_eq_bot_of_countable {K : Subgroup G} (hK : (K : Set G).Countable) :
    TauCeti.Lie.lieSubalgebraOfSubgroup (I := I) K = ⊥ := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact lieSubalgebraOfSubgroup_eq_bot_of_isTotallyDisconnected hK.isTotallyDisconnected


end TauCeti.Lie
