/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.GroupTheory.GroupAction.FixedPoints

/-!
# Topology of additive fixed points

The fixed points of a subgroup carry the subspace topology from the coefficient space. This file
proves continuity of restricted biadditive pairings and supplies the continuous quotient actions
used by invariant coefficients. Continuity of the inclusion into the ambient coefficient space
follows from Mathlib's generic `continuous_subtype_val`, for additive monoids as well as groups.

For a normal subgroup `H`, the algebraic `G ⧸ H`-action on the fixed points of `H` is supplied by
`TauCeti/GroupTheory/GroupAction/FixedPoints.lean`. If the coefficients are discrete and `H` is
open, the quotient is discrete, so its action is continuous without a continuity assumption on
the ambient action. For an arbitrary normal `H`, a continuous ambient action also descends to a
continuous quotient action on discrete fixed points. The latter uses only the quotient topology,
with no compatibility assumption on the topology and group structure of `G`.

The fixed points of open normal subgroups form a directed family, growing as the subgroup
shrinks. Together with quotient-action continuity, this gives the coefficient system used in
finite-quotient descriptions of continuous cohomology.

Pairings and quotient-action continuity have both additive-submonoid and additive-subgroup
forms. The subgroup forms retain the coefficient groups' additive inverses and match the
subgroup carrier used by group cohomology.

## Main results

* `Subgroup.continuous_fixedPointsAddSubmonoidPairing` and
  `Subgroup.continuous_fixedPointsPairing`: restriction of a jointly continuous equivariant
  biadditive pairing remains jointly continuous.
* `TauCeti.directed_fixedPoints_addSubmonoid` and `TauCeti.directed_fixedPoints_addSubgroup`:
  fixed points of open normal subgroups form a directed family.
* `TauCeti.continuousSMulQuotientFixedPointsAddSubmonoid` and
  `TauCeti.continuousSMulQuotientFixedPoints`: quotient actions on discrete fixed points of open
  normal subgroups are continuous.
* `TauCeti.continuousSMulQuotientFixedPointsAddSubmonoidOfContinuousSMul` and
  `TauCeti.continuousSMulQuotientFixedPointsOfContinuousSMul`: quotient actions on discrete fixed
  points of arbitrary normal subgroups are continuous when the ambient action is continuous.
* `TauCeti.continuous_fixedPoints_addSubgroup_subtype`: the inclusion of the fixed-point additive
  subgroup into the ambient coefficient group is continuous.
-/

public section

open MulAction

namespace Subgroup

section Pairing

variable {G : Type*} [Group G]
  {M : Type*} [AddMonoid M] [TopologicalSpace M] [DistribMulAction G M]
  {N : Type*} [AddMonoid N] [TopologicalSpace N] [DistribMulAction G N]
  {P : Type*} [AddCommMonoid P] [TopologicalSpace P] [DistribMulAction G P]

/-- Restricting a jointly continuous `H`-equivariant pairing to invariant coefficients remains
jointly continuous. -/
theorem continuous_fixedPointsAddSubmonoidPairing (H : Subgroup G) (μ : M →+ N →+ P)
    (hequiv : ∀ (h : H) (m : M) (n : N),
      μ ((h : G) • m) ((h : G) • n) = (h : G) • μ m n)
    (hμ : Continuous fun p : M × N => μ p.1 p.2) :
    Continuous fun p : FixedPoints.addSubmonoid H M × FixedPoints.addSubmonoid H N =>
      fixedPointsAddSubmonoidPairing H μ hequiv p.1 p.2 := by
  refine continuous_induced_rng.2 ?_
  simpa only [Function.comp_def, coe_fixedPointsAddSubmonoidPairing,
    Prod.map_fst, Prod.map_snd] using
    hμ.comp (continuous_subtype_val.prodMap continuous_subtype_val)

end Pairing

section PairingAddGroup

variable {G : Type*} [Group G]
  {M : Type*} [AddGroup M] [TopologicalSpace M] [DistribMulAction G M]
  {N : Type*} [AddGroup N] [TopologicalSpace N] [DistribMulAction G N]
  {P : Type*} [AddCommGroup P] [TopologicalSpace P] [DistribMulAction G P]

/-- Restricting a jointly continuous `H`-equivariant pairing to the fixed-point additive subgroups
remains jointly continuous. -/
theorem continuous_fixedPointsPairing (H : Subgroup G) (μ : M →+ N →+ P)
    (hequiv : ∀ (h : H) (m : M) (n : N),
      μ ((h : G) • m) ((h : G) • n) = (h : G) • μ m n)
    (hμ : Continuous fun p : M × N => μ p.1 p.2) :
    Continuous fun p : FixedPoints.addSubgroup H M × FixedPoints.addSubgroup H N =>
      fixedPointsPairing H μ hequiv p.1 p.2 := by
  refine (continuous_fixedPointsAddSubmonoidPairing H μ hequiv hμ).congr fun p ↦ ?_
  apply Subtype.ext
  exact (coe_fixedPointsAddSubmonoidPairing H μ hequiv p.1 p.2).trans
    (coe_fixedPointsPairing H μ hequiv p.1 p.2).symm

end PairingAddGroup

end Subgroup

namespace TauCeti

section FiniteLevel

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddMonoid M] [DistribMulAction G M]

/-- The finite-level fixed-point additive submonoids form a directed family: the open normal
subgroups are closed under intersection, and the fixed points grow as the subgroup shrinks. -/
theorem directed_fixedPoints_addSubmonoid :
    Directed (· ≤ ·) fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubmonoid U.toSubgroup M :=
  Antitone.directed_le fun _ _ h ↦ fixedPoints_subgroup_antitone G M h

variable [TopologicalSpace M] [DiscreteTopology M] [SeparatelyContinuousMul G]

/-- For an open normal subgroup `U`, the action of the discrete quotient on the fixed-point
additive submonoid is continuous. -/
instance continuousSMulQuotientFixedPointsAddSubmonoid (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubmonoid U.toSubgroup M) :=
  ⟨continuous_of_discreteTopology⟩

end FiniteLevel

section FiniteLevelAddGroup

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddGroup M] [DistribMulAction G M]

/-- The finite-level invariants form a directed family: the open normal subgroups are closed under
intersection, and the invariants grow as the subgroup shrinks. The corresponding cohomology tower
is filtered for this reason. -/
theorem directed_fixedPoints_addSubgroup :
    Directed (· ≤ ·) fun U : OpenNormalSubgroup G ↦ FixedPoints.addSubgroup U.toSubgroup M :=
  directed_fixedPoints_addSubmonoid G M

variable [SeparatelyContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]

/-- For an open normal subgroup `U` the action of the discrete quotient group `G ⧸ U` on the
invariant coefficients `M ^ U` is continuous. -/
instance continuousSMulQuotientFixedPoints (U : OpenNormalSubgroup G) :
    ContinuousSMul (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) :=
  inferInstanceAs <| ContinuousSMul (G ⧸ U.toSubgroup)
    (FixedPoints.addSubmonoid U.toSubgroup M)

end FiniteLevelAddGroup

section Subtype

variable (G : Type*) [Group G] (M : Type*) [AddGroup M] [DistribMulAction G M]
variable [TopologicalSpace M]

/-- The inclusion `M ^ H ↪ M` of the invariants is continuous for the subspace topology. -/
theorem continuous_fixedPoints_addSubgroup_subtype (H : Subgroup G) :
    Continuous ⇑(FixedPoints.addSubgroup H M).subtype :=
  continuous_subtype_val

end Subtype

section ArbitraryNormalSubgroup

variable (G : Type*) [Group G] [TopologicalSpace G]
variable (M : Type*) [AddMonoid M] [DistribMulAction G M]
variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- For an arbitrary normal subgroup `H`, the action of `G ⧸ H` on the invariants `M ^ H` of a
discrete module is continuous. Unlike
`TauCeti.continuousSMulQuotientFixedPoints`, which reads the continuity off the discreteness of
`G ⧸ H` for open `H` and needs no continuity of the `G`-action, this deduces it from continuity of
the `G`-action: the invariants are discrete, so continuity is continuity in the group variable
alone, and there it is the continuity of the `G`-action read through the quotient map. No
compatibility of the topology of `G` with its group structure is needed, since `G ⧸ H` carries the
quotient topology. -/
instance continuousSMulQuotientFixedPointsAddSubmonoidOfContinuousSMul (H : Subgroup G) [H.Normal] :
    ContinuousSMul (G ⧸ H) (FixedPoints.addSubmonoid H M) where
  continuous_smul := by
    rw [continuous_prod_of_discrete_right]
    intro m
    refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ?_
    refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
    exact (continuous_id.smul continuous_const : Continuous fun g : G => g • (m : M))

/-- For an arbitrary normal subgroup `H`, the quotient acts continuously on the fixed-point
additive subgroup of a discrete module with continuous `G`-action. -/
instance continuousSMulQuotientFixedPointsOfContinuousSMul (G : Type*) [Group G]
    [TopologicalSpace G] (M : Type*) [AddGroup M] [DistribMulAction G M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
    (H : Subgroup G) [H.Normal] :
    ContinuousSMul (G ⧸ H) (FixedPoints.addSubgroup H M) :=
  inferInstanceAs <| ContinuousSMul (G ⧸ H) (FixedPoints.addSubmonoid H M)

end ArbitraryNormalSubgroup

end TauCeti
