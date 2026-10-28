/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Left

/-!
# Restricted products of groups away from a set of indices

This file names the restricted product of a family of groups relative to a family of reference
subgroups over the indices outside a set `S`. This is the shape in which restricted products
appear when the local groups at a finite set of places are set apart from the rest of an adelic
group: the finite adelic points away from a finite set of places.

It then constructs the restriction homomorphism from the restricted product to the restricted
product away from `S`, which forgets the coordinates indexed by `S`. This is Mathlib's
`RestrictedProduct.mapAlongMonoidHom` along the inclusion `{i // i ∉ S} → ι`, which carries the
cofinite filter to the cofinite filter because it is injective. Its coordinate formula, its
continuity for every reference family, and its compatibility with nested index sets are the
facts the decomposition `awayDecomposition` of a restricted product along a finite set of indices
needs.

No finiteness of `S` is assumed anywhere: the away-`S` restricted product and the restriction to
it make sense for every set of indices.

When `S` is empty, `awayEmptyEquiv` is the canonical reindexing to the original restricted
product, with inverse `restrictAway ∅`. Both directions are continuous for every reference family;
`awayEmptyContinuousMulEquiv` packages them as an isomorphism of topological groups. Its additive
counterpart is `addAwayEmptyContinuousAddEquiv`.

Everything here is also stated for additive groups (`RestrictedProductAddGroupAway`,
`addRestrictAway`, …).

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
* The canonical empty-away convention of
  [OrthogonalSpinGroups roadmap correction #1673](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1673).
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The restricted product of `G` relative to `U` over the indices **outside** `S`. This is
`RestrictedProductGroup` at the index type `{i // i ∉ S}`; no finiteness of `S` is needed to form
it. -/
@[to_additive /-- The restricted product of the family of additive groups `G` relative to `U` over
the indices **outside** `S`. This is `RestrictedProductAddGroup` at the index type
`{i // i ∉ S}`; no finiteness of `S` is needed to form it. -/]
abbrev RestrictedProductGroupAway (S : Set ι) (U : ∀ i, Subgroup (G i)) :=
  RestrictedProductGroup fun i : {i // i ∉ S} ↦ U i.1

/-- Restriction of a restricted product to the indices outside `S`, forgetting the coordinates
indexed by `S`. -/
@[to_additive addRestrictAway /-- Restriction of a restricted product of additive groups to the
indices outside `S`, forgetting the coordinates indexed by `S`. -/]
def restrictAway (S : Set ι) (U : ∀ i, Subgroup (G i)) :
    RestrictedProductGroup U →* RestrictedProductGroupAway S U :=
  RestrictedProduct.mapAlongMonoidHom G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun i ↦ MonoidHom.id (G i.1))
    (.of_forall fun _ _ hx ↦ hx)

/-- The restriction away from `S` keeps the coordinates outside `S` unchanged. -/
@[to_additive (attr := simp) addRestrictAway_apply /-- The restriction away from `S` of a restricted
product of additive groups keeps the coordinates outside `S` unchanged. -/]
theorem restrictAway_apply (S : Set ι) (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) (i : {i // i ∉ S}) :
    restrictAway S U x i = x i.1 :=
  RestrictedProduct.mapAlongMonoidHom_apply G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite (fun i ↦ MonoidHom.id (G i.1))
    (.of_forall fun _ _ hx ↦ hx) x i

/-- Removing an empty set of indices recovers the original restricted product, by the canonical
reindexing which forgets the vacuous proof that an index is outside the empty set. -/
@[to_additive addAwayEmptyEquiv /-- Removing an empty set of indices recovers the original
restricted product of additive groups, by the canonical reindexing which forgets the vacuous
proof that an index is outside the empty set. -/]
def awayEmptyEquiv (U : ∀ i, Subgroup (G i)) :
    RestrictedProductGroupAway (∅ : Set ι) U ≃* RestrictedProductGroup U :=
  restrictedProductCongrLeft U (Equiv.subtypeUnivEquiv fun i ↦ Set.notMem_empty i)

/-- The empty-away comparison preserves each coordinate. -/
@[to_additive (attr := simp) addAwayEmptyEquiv_apply]
theorem awayEmptyEquiv_apply (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroupAway (∅ : Set ι) U) (i : ι) :
    awayEmptyEquiv U x i = x ⟨i, Set.notMem_empty i⟩ := by
  unfold awayEmptyEquiv
  exact restrictedProductCongrLeft_apply_apply U
    (Equiv.subtypeUnivEquiv fun i ↦ Set.notMem_empty i) x ⟨i, Set.notMem_empty i⟩

/-- Restriction away from the empty set is the inverse of the canonical comparison. -/
@[to_additive (attr := simp) addAwayEmptyEquiv_restrictAway]
theorem awayEmptyEquiv_restrictAway (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) : awayEmptyEquiv U (restrictAway ∅ U x) = x := by
  ext i
  simp

/-- The inverse empty-away comparison is restriction away from the empty set. -/
@[to_additive (attr := simp) addAwayEmptyEquiv_symm_apply]
theorem awayEmptyEquiv_symm_apply (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) :
    (awayEmptyEquiv U).symm x = restrictAway ∅ U x := by
  apply (awayEmptyEquiv U).injective
  simp

/-- The canonical empty-away comparison is continuous for every reference family. -/
@[to_additive continuous_addAwayEmptyEquiv]
theorem continuous_awayEmptyEquiv [∀ i, TopologicalSpace (G i)]
    (U : ∀ i, Subgroup (G i)) : Continuous (awayEmptyEquiv U) :=
  continuous_restrictedProductCongrLeft U _

/-- The inverse empty-away comparison is continuous for every reference family. -/
@[to_additive continuous_addAwayEmptyEquiv_symm]
theorem continuous_awayEmptyEquiv_symm [∀ i, TopologicalSpace (G i)]
    (U : ∀ i, Subgroup (G i)) : Continuous (awayEmptyEquiv U).symm :=
  continuous_restrictedProductCongrLeft_symm U _

/-- The canonical empty-away comparison as an isomorphism of topological groups. -/
@[to_additive addAwayEmptyContinuousAddEquiv /-- The canonical empty-away comparison as an
isomorphism of topological additive groups. -/]
def awayEmptyContinuousMulEquiv [∀ i, TopologicalSpace (G i)] (U : ∀ i, Subgroup (G i)) :
    RestrictedProductGroupAway (∅ : Set ι) U ≃ₜ* RestrictedProductGroup U where
  toMulEquiv := awayEmptyEquiv U
  continuous_toFun := continuous_awayEmptyEquiv U
  continuous_invFun := continuous_awayEmptyEquiv_symm U

/-- The topological empty-away comparison has the canonical reindexing as underlying map. -/
@[to_additive (attr := simp) addAwayEmptyContinuousAddEquiv_apply]
theorem awayEmptyContinuousMulEquiv_apply [∀ i, TopologicalSpace (G i)]
    (U : ∀ i, Subgroup (G i)) (x : RestrictedProductGroupAway (∅ : Set ι) U) :
    awayEmptyContinuousMulEquiv U x = awayEmptyEquiv U x := by rfl

/-- The inverse topological comparison is restriction away from the empty set. -/
@[to_additive (attr := simp) addAwayEmptyContinuousAddEquiv_symm_apply]
theorem awayEmptyContinuousMulEquiv_symm_apply [∀ i, TopologicalSpace (G i)]
    (U : ∀ i, Subgroup (G i)) (x : RestrictedProductGroup U) :
    (awayEmptyContinuousMulEquiv U).symm x = restrictAway ∅ U x := by
  apply (awayEmptyContinuousMulEquiv U).injective
  rw [ContinuousMulEquiv.apply_symm_apply, awayEmptyContinuousMulEquiv_apply,
    awayEmptyEquiv_restrictAway]

/-- Restricting away from a larger set factors through restricting away from a smaller one:
the coordinate of `restrictAway T U x` at `i ∉ T` is the coordinate of `restrictAway S U x` at
the same index, viewed outside `S ⊆ T`. -/
@[to_additive addRestrictAway_addRestrictAway /-- Restricting a restricted product of additive
groups away from a larger set factors through restricting away from a smaller one: the coordinate of
`addRestrictAway T U x` at `i ∉ T` is the coordinate of `addRestrictAway S U x` at the same index,
viewed outside `S ⊆ T`. -/]
theorem restrictAway_restrictAway {S T : Set ι} (hST : S ⊆ T) (U : ∀ i, Subgroup (G i))
    (x : RestrictedProductGroup U) (i : {i // i ∉ T}) :
    restrictAway T U x i = restrictAway S U x ⟨i.1, fun hi ↦ i.2 (hST hi)⟩ := by
  simp

/-- The restriction away from `S` is continuous for every reference family: it is a map out of a
single restricted product whose coordinate maps are identities. -/
@[to_additive continuous_addRestrictAway /-- The restriction away from `S` of a restricted product
of additive groups is continuous for every reference family: it is a map out of a single restricted
product whose coordinate maps are identities. -/]
theorem continuous_restrictAway [∀ i, TopologicalSpace (G i)] (S : Set ι)
    (U : ∀ i, Subgroup (G i)) :
    Continuous (restrictAway S U) :=
  RestrictedProduct.mapAlong_continuous G (fun i : {i // i ∉ S} ↦ G i.1) Subtype.val
    Subtype.val_injective.tendsto_cofinite
    (fun i ↦ (MonoidHom.id (G i.1) : G i.1 → G i.1)) (.of_forall fun _ _ hx ↦ hx)
    fun _ ↦ continuous_id

end TauCeti
