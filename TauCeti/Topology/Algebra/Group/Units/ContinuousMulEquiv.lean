/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Topological isomorphisms to embedded subgroups of units

An algebraic isomorphism from a group with continuous inversion to a subgroup of monoid units
is a homeomorphism when its underlying map to the monoid is a topological embedding. The
continuous upgrade retains the supplied algebraic equivalence and the original topologies.
The same statements hold for additive groups, additive units and continuous negation.

## Main declarations

* `MulEquiv.toContinuousMulEquivOfUnits`: the continuous upgrade of the supplied isomorphism.
* `MulEquiv.toMulEquiv_toContinuousMulEquivOfUnits`: its underlying algebraic equivalence.
* `MulEquiv.toContinuousMulEquivOfUnits_apply` and
  `MulEquiv.toContinuousMulEquivOfUnits_symm_apply`: its forward and inverse computation rules.
* `AddEquiv.toContinuousAddEquivOfAddUnits`: the additive counterpart.
* `AddEquiv.toAddEquiv_toContinuousAddEquivOfAddUnits`,
  `AddEquiv.toContinuousAddEquivOfAddUnits_apply` and
  `AddEquiv.toContinuousAddEquivOfAddUnits_symm_apply`: its computation rules.

## References

* Mathlib, `Topology/Algebra/Group/Units.lean`, for the topology and continuity criteria on units.
* Mathlib, `Topology/Algebra/ContinuousMonoidHom.lean`, for continuous algebraic isomorphisms.
-/

public section

open Topology

namespace MulEquiv

variable {G M : Type*} [Group G] [Monoid M]
  [TopologicalSpace G] [TopologicalSpace M] [ContinuousInv G] {K : Subgroup Mˣ}

/-- An isomorphism from a group with continuous inversion to a subgroup of monoid units is a
homeomorphism if its underlying map to the monoid is a topological embedding. -/
@[to_additive /-- An isomorphism from an additive group with continuous negation to an additive
subgroup of additive units is a homeomorphism if its map to the monoid is an embedding. -/]
def toContinuousMulEquivOfUnits (e : G ≃* K)
    (he : IsEmbedding (fun x ↦ ((e x : Mˣ) : M))) : G ≃ₜ* K where
  __ := e
  continuous_toFun := by
    let f : G →* Mˣ := K.subtype.comp e.toMonoidHom
    have hc : Continuous f := Units.continuous_iff.2
      ⟨he.continuous, (he.continuous.comp continuous_inv).congr fun x ↦
        congrArg Units.val (map_inv f x)⟩
    exact hc.subtype_mk _
  continuous_invFun := by
    apply he.continuous_iff.2
    exact (Units.continuous_val.comp continuous_subtype_val).congr fun x ↦
      (congrArg (fun y : K ↦ ((y : Mˣ) : M)) (e.apply_symm_apply x)).symm

/-- The continuous upgrade preserves the supplied algebraic equivalence. -/
@[to_additive (attr := simp) /-- The continuous upgrade preserves the supplied additive
algebraic equivalence. -/]
theorem toMulEquiv_toContinuousMulEquivOfUnits (e : G ≃* K)
    (he : IsEmbedding (fun x ↦ ((e x : Mˣ) : M))) :
    (e.toContinuousMulEquivOfUnits he : G ≃* K) = e := by
  unfold toContinuousMulEquivOfUnits
  rfl

/-- The continuous upgrade has the same values as the supplied algebraic equivalence. -/
@[to_additive (attr := simp) /-- The continuous upgrade has the same values as the supplied
additive algebraic equivalence. -/]
theorem toContinuousMulEquivOfUnits_apply (e : G ≃* K)
    (he : IsEmbedding (fun x ↦ ((e x : Mˣ) : M))) (x : G) :
    e.toContinuousMulEquivOfUnits he x = e x := by
  unfold toContinuousMulEquivOfUnits
  rfl

/-- The inverse continuous upgrade has the same values as the original inverse equivalence. -/
@[to_additive (attr := simp) /-- The inverse continuous upgrade has the same values as the
original inverse additive equivalence. -/]
theorem toContinuousMulEquivOfUnits_symm_apply (e : G ≃* K)
    (he : IsEmbedding (fun x ↦ ((e x : Mˣ) : M))) (x : K) :
    (e.toContinuousMulEquivOfUnits he).symm x = e.symm x := by
  unfold toContinuousMulEquivOfUnits
  rfl

end MulEquiv
