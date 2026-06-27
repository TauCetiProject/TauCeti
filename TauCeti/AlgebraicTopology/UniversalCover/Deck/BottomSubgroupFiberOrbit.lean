/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbitQuotientGroup

/-!
# Fibre orbits for the trivial deck subgroup

The subgroup-fibre orbit quotient API treats `SubgroupFiberOrbitQuotient H b` uniformly for
all subgroups `H ≤ Deck p`. The basic bottom-subgroup equivalence lives in
`SubgroupFiberOrbit.lean`; this file records its compatibility with the quotient-group
comparison layer.

This is small bookkeeping for the universal-covers roadmap. In Stage 2, the cover associated
to a subgroup `H ≤ π₁(X, x₀)` has the universal cover as the `H = ⊥` case, while the
regular-cover computation compares subgroup fibre quotients with deck-group quotients. The
lemmas here let later arguments use that specialization without unfolding the orbit relation
or the quotient construction.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitClass_bot_eq_iff`: equality of bottom-subgroup classes is
  equality of fibre points.
* Compatibility lemmas under the free-transitive and regular-cover quotient-group
  equivalences to `Deck p ⧸ ⊥`.

## References

This supplies a prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 7:
the cover associated to `H ≤ π₁(X, x₀)` and its pointed basepoint bookkeeping. It is only a
deck-specific specialization of Mathlib's orbit-quotient and quotient-group APIs; no Mathlib
infrastructure is vendored.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- Under the free-transitive deck-action quotient-group equivalence, the bottom-subgroup
class of `φ⁻¹ • e` corresponds to the quotient class of `φ`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (Deck p)) e
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ⁻¹ • e)) =
      QuotientGroup.mk (s := (⊥ : Subgroup (Deck p))) φ := by
  rw [subgroupFiberOrbitQuotientBotEquiv_symm_apply,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul]

/-- Under the free-transitive deck-action quotient-group equivalence, the bottom-subgroup
class of `φ • e` corresponds to the quotient class of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (Deck p)) e
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ • e)) =
      QuotientGroup.mk (s := (⊥ : Subgroup (Deck p))) φ⁻¹ := by
  rw [subgroupFiberOrbitQuotientBotEquiv_symm_apply,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]

/-- Composing the bottom-subgroup fibre quotient equivalence with `G / ⊥ ≃ G` sends the
class of `φ • e` to `φ⁻¹`, matching the convention of
`MulAction.equivSubgroupOrbitsQuotientGroup`. -/
@[simp]
lemma quotientBot_subgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) :
    QuotientGroup.quotientBot
        (subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (Deck p)) e
          ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ • e))) =
      φ⁻¹ := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul]
  rfl

/-- The regular-cover specialization of the bottom-subgroup quotient-group equivalence sends
the class of `φ • e` to the quotient class of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg (⊥ : Subgroup (Deck p)) e
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ • e)) =
      QuotientGroup.mk (s := (⊥ : Subgroup (Deck p))) φ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  rw [subgroupFiberOrbitQuotientBotEquiv_symm_apply,
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]

/-- Composing the regular bottom-subgroup fibre quotient equivalence with `G / ⊥ ≃ G` sends
the class of `φ • e` to `φ⁻¹`. -/
@[simp]
lemma quotientBot_regularSubgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : Deck p) :
    QuotientGroup.quotientBot
        (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg
          (⊥ : Subgroup (Deck p)) e
          ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ • e))) =
      φ⁻¹ := by
  rw [regularSubgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_smul]
  rfl

end Deck

end TauCeti
