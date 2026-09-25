/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Algebra.GroupAction.QuotientAddGroup

/-!
# Continuity of the action on a stable additive subgroup

Let a monoid `G` act continuously and distributively on a topological additive group `M`, and
let `N` be a `G`-stable additive subgroup of `M`. The restricted action
`AddSubgroup.restrictDistribMulAction` of `G` on `N` is continuous for the subspace topology,
because the inclusion of `N` in `M` is an equivariant topological embedding. Mathlib records this
as the instance `SMulMemClass.continuousSMul` when the stability is part of a `SMulMemClass`
structure; here the stability is a hypothesis, so the continuity is a theorem about the restricted
action.

## Main results

* `AddSubgroup.restrictDistribMulAction_continuousSMul`: the restricted action of `G` on a
  `G`-stable additive subgroup is continuous.
-/

public section

namespace TauCeti

variable {G : Type*} [Monoid G] [TopologicalSpace G] {M : Type*} [AddGroup M]
  [TopologicalSpace M] [DistribMulAction G M] [ContinuousSMul G M]

/-- The restricted action `AddSubgroup.restrictDistribMulAction` of `G` on a `G`-stable additive
subgroup `N` of `M` is continuous for the subspace topology on `N`. -/
theorem _root_.AddSubgroup.restrictDistribMulAction_continuousSMul (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) :
    letI := N.restrictDistribMulAction hN
    ContinuousSMul G N :=
  letI := N.restrictDistribMulAction hN
  Topology.IsInducing.subtypeVal.continuousSMul continuous_id fun {_ _} ↦ rfl

end TauCeti
