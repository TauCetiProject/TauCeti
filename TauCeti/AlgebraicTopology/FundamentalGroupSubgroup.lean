/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Subgroups of the fundamental group under basepoint change

The classification of connected covers records, for a pointed cover, a subgroup of
`π₁(X, x₀)`. Changing the basepoint along a path transports this subgroup by the usual
basepoint-change isomorphism. This file packages that transport, together with the membership,
coercion, and normality API needed by the universal-covers roadmap's pointed/unpointed
bookkeeping.

Mathlib already provides the basepoint-change equivalence
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are only the
subgroup-level spelling of mapping a subgroup along that equivalence. The transport `def`s are
left unexposed, so downstream their bodies stay hidden and consumers go through the membership,
coercion, and normality lemmas rather than unfolding to `Subgroup.map`/`MulEquiv.subgroupMap`.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  to a subgroup of `π₁(X, x₁)` along a path from `x₀` to `x₁`.
* `TauCeti.FundamentalGroup.basepointChangeSubgroupEquiv`: the induced multiplicative
  equivalence between the original subgroup and its transported subgroup.
* `TauCeti.FundamentalGroup.normal_basepointChangeSubgroup_iff`: normality is invariant under
  basepoint change.

## References

This supplies a small algebraic prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 2, items 7 and 8: the recovered subgroup of a pointed cover transforms by conjugacy under
basepoint change, and unpointed connected covers are classified by conjugacy classes of
subgroups.
-/

public section

noncomputable section

namespace TauCeti

namespace FundamentalGroup

open scoped FundamentalGroupoid

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- Transport a subgroup of `π₁(X, x₀)` to a subgroup of `π₁(X, x₁)` along a path from `x₀`
to `x₁`, by mapping along the basepoint-change equivalence. Kept unexposed so consumers go
through the membership and coercion API below rather than unfolding to `Subgroup.map`. -/
def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  H.map (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ : _ →* _)

/-- Membership in a basepoint-changed subgroup, expressed by transporting back along the
inverse basepoint-change equivalence. -/
@[simp]
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : _root_.FundamentalGroup X x₁) :
    η ∈ basepointChangeSubgroup γ H ↔
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm η ∈ H :=
  Subgroup.mem_map_equiv

/-- The image of an element of `H` under basepoint change lies in the transported subgroup. -/
lemma mem_basepointChangeSubgroup_of_mem (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : _root_.FundamentalGroup X x₀)
    (hη : η ∈ H) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η ∈
      basepointChangeSubgroup γ H :=
  Subgroup.mem_map_of_mem _ hη

/-- Transporting subgroups by basepoint change preserves and reflects inclusion. -/
@[simp]
lemma basepointChangeSubgroup_le_iff (γ : Path x₀ x₁)
    (H K : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K ↔ H ≤ K := by
  constructor
  · intro h η hη
    have hmem :
        _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η ∈
          basepointChangeSubgroup γ K :=
      h (mem_basepointChangeSubgroup_of_mem γ H η hη)
    simpa using (mem_basepointChangeSubgroup_iff γ K
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η)).mp hmem
  · intro h η hη
    exact (mem_basepointChangeSubgroup_iff γ K η).mpr
      (h ((mem_basepointChangeSubgroup_iff γ H η).mp hη))

/-- The basepoint-change equivalence restricts to an equivalence from a subgroup to its
transported subgroup. Kept unexposed so consumers use the coercion lemmas below rather than
unfolding to `MulEquiv.subgroupMap`. -/
def basepointChangeSubgroupEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    H ≃* basepointChangeSubgroup γ H :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).subgroupMap H

/-- On underlying loop classes, the subgroup equivalence is the usual basepoint-change
equivalence. -/
@[simp]
lemma basepointChangeSubgroupEquiv_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : H) :
    (basepointChangeSubgroupEquiv γ H η : _root_.FundamentalGroup X x₁) =
      _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η.1 :=
  MulEquiv.coe_subgroupMap_apply _ H η

/-- The inverse subgroup equivalence is the inverse basepoint-change equivalence on underlying
loop classes. -/
@[simp]
lemma basepointChangeSubgroupEquiv_symm_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : basepointChangeSubgroup γ H) :
    ((basepointChangeSubgroupEquiv γ H).symm η : _root_.FundamentalGroup X x₀) =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm η.1 :=
  congrArg Subtype.val
    (MulEquiv.subgroupMap_symm_apply
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) H η)

/-- A subgroup is normal exactly when its basepoint-changed subgroup is normal. -/
@[simp]
lemma normal_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    (basepointChangeSubgroup γ H).Normal ↔ H.Normal :=
  MulEquiv.normal_map_iff

end FundamentalGroup

end TauCeti

end
