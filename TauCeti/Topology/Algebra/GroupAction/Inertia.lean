/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction

/-!
# Closedness of inertia groups

Let a group `G` with a topology act continuously on a topological additive group `M`. The inertia
group `AddSubgroup.inertia` of an additive subgroup `I` of `M` consists of the `g` acting trivially
modulo `I`, that is, with `g • x - x ∈ I` for every `x`. If `I` is closed, each such condition cuts
out a closed subset of `G`, so the inertia group is closed. For an ideal of a ring with the
discrete topology every ideal is closed, which gives closedness of the inertia groups of ideals.

## Main results

* `AddSubgroup.isClosed_inertia`: the inertia group of a closed additive subgroup is closed.
-/

public section

/-- **Inertia groups are closed.** If `G` acts continuously on a topological additive group `M`,
then the inertia group of a closed additive subgroup `I` of `M`, the `g` with `g • x - x ∈ I` for
every `x`, is closed in `G`. -/
theorem AddSubgroup.isClosed_inertia {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} [AddGroup M] [MulAction G M] [TopologicalSpace M]
    [ContinuousSub M] [ContinuousSMul G M] {I : AddSubgroup M} (hI : IsClosed (I : Set M)) :
    IsClosed (I.inertia G : Set G) := by
  have : (I.inertia G : Set G) = ⋂ x : M, (fun g : G ↦ g • x - x) ⁻¹' I := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun _ ↦ hI.preimage ((continuous_id.smul continuous_const).sub
    continuous_const)
