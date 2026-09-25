/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Algebra.GroupAction.QuotientAddGroup

/-!
# Continuity of the actions on a stable additive subgroup and on its quotient

Let a monoid `G` act continuously and distributively on a topological additive group `M`, and
let `N` be a `G`-stable additive subgroup of `M`. The restricted action
`AddSubgroup.restrictDistribMulAction` of `G` on `N` is continuous for the subspace topology,
because the inclusion of `N` in `M` is an equivariant topological embedding. Mathlib records this
as the instance `SMulMemClass.continuousSMul` when the stability is part of a `SMulMemClass`
structure; here the stability is a hypothesis, so the continuity is a theorem about the restricted
action.

When `M` is commutative with separately continuous addition, the quotient action
`AddSubgroup.quotientDistribMulAction` of `G` on `M ⧸ N` is continuous for the quotient topology
as well, because the quotient map `M → M ⧸ N` is an open quotient map and the action on `M ⧸ N` is
the descent of the continuous map `(g, x) ↦ ↑(g • x)` along `G × M → G × (M ⧸ N)`.

## Main results

* `AddSubgroup.restrictDistribMulAction_continuousSMul`: the restricted action of `G` on a
  `G`-stable additive subgroup is continuous.
* `AddSubgroup.quotientDistribMulAction_continuousSMul`: the quotient action of `G` on the
  quotient by a `G`-stable additive subgroup is continuous.
-/

public section

namespace TauCeti

variable {G : Type*} [Monoid G] [TopologicalSpace G] {M : Type*}

section AddGroup

variable [AddGroup M] [TopologicalSpace M] [DistribMulAction G M] [ContinuousSMul G M]

/-- The restricted action `AddSubgroup.restrictDistribMulAction` of `G` on a `G`-stable additive
subgroup `N` of `M` is continuous for the subspace topology on `N`. -/
theorem _root_.AddSubgroup.restrictDistribMulAction_continuousSMul (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) :
    letI := N.restrictDistribMulAction hN
    ContinuousSMul G N :=
  letI := N.restrictDistribMulAction hN
  Topology.IsInducing.subtypeVal.continuousSMul continuous_id fun {_ _} ↦ rfl

end AddGroup

section AddCommGroup

variable [AddCommGroup M] [TopologicalSpace M] [SeparatelyContinuousAdd M] [DistribMulAction G M]
  [ContinuousSMul G M]

/-- The quotient action `AddSubgroup.quotientDistribMulAction` of `G` on the quotient `M ⧸ N` by
a `G`-stable additive subgroup `N` is continuous for the quotient topology on `M ⧸ N`. -/
theorem _root_.AddSubgroup.quotientDistribMulAction_continuousSMul (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) :
    letI := N.quotientDistribMulAction hN
    ContinuousSMul G (M ⧸ N) := by
  let := N.quotientDistribMulAction hN
  refine ⟨?_⟩
  rw [← (IsOpenQuotientMap.id.prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := N))).continuous_comp_iff]
  exact (QuotientAddGroup.continuous_mk.comp continuous_smul).congr fun x ↦
    (N.quotientDistribMulAction_smul_mk hN x.1 x.2).symm

end AddCommGroup

end TauCeti
