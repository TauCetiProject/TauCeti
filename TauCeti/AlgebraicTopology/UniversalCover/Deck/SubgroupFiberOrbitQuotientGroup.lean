/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit

/-!
# Subgroup fibre orbits of a regular cover as deck-group quotients

For a regular preconnected covering map, evaluation at any point of a fibre identifies the
deck group with that fibre. This file records the corresponding quotient-level statement:
orbits of a subgroup `H ≤ Deck p` on the fibre are equivalent to the coset quotient
`Deck p ⧸ H`.

This is bookkeeping for the universal-covers roadmap. The classification of connected covers
uses fibre quotients by subgroups, while the regular-cover computation of the deck group of
the cover attached to `H` is expressed algebraically as a normalizer quotient. The bridge here
lets later arguments move between those fibre-orbit quotients and subgroup quotients without
unfolding either construction.

## Main declarations

* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivQuotientGroup`: for a regular
  preconnected covering, `SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H`.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk`: the inverse
  sends the coset of `φ` to the `H`-orbit class of `φ⁻¹ • e`.

## References

This supplies a prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, items
7 and 8, especially the regular-cover milestones comparing fibre quotients with the
normalizer quotient `N(H)/H`. It is a deck-specific specialization of Mathlib's
`MulAction.equivSubgroupOrbitsQuotientGroup`, the orbit-quotient form of the
orbit-stabilizer theorem for free transitive actions.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

/-- For a regular preconnected covering, quotienting one fibre by the action of
`H ≤ Deck p` is equivalent to the coset quotient `Deck p ⧸ H`.

The chosen point `e` fixes the identification between the deck group and the fibre. With
Mathlib's convention for `MulAction.equivSubgroupOrbitsQuotientGroup`, the inverse sends the
coset of `φ` to the orbit class of `φ⁻¹ • e`; see
`regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk`. -/
@[expose] noncomputable def regularSubgroupFiberOrbitQuotientEquivQuotientGroup
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact MulAction.equivSubgroupOrbitsQuotientGroup e H

/-- The inverse quotient equivalence sends the coset of a deck transformation `φ` to the
`H`-orbit class of the point `φ⁻¹ • e`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  rfl

/-- On underlying points, the inverse quotient equivalence sends the coset of `φ` to the
class of the value of `φ⁻¹` on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  rw [regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk]
  congr 1

/-- The inverse quotient equivalence sends the identity coset to the orbit class of the chosen
fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk (s := H) (1 : Deck p)) =
      subgroupFiberOrbitClass H e := by
  rw [regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk, inv_one, one_smul]

/-- The quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset of `φ`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  simpa using
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).apply_symm_apply
      (QuotientGroup.mk (s := H) φ)

/-- The quotient equivalence sends the chosen fibre point to the identity coset. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : Deck p) := by
  simpa using
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
      hp hreg H e (1 : Deck p)

/-- The quotient equivalence sends the orbit class of `φ • e` to the coset of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  simpa using
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
      hp hreg H e φ⁻¹

/-- Equality of subgroup fibre-orbit classes is equality of the corresponding deck cosets
under the regular-cover quotient equivalence. -/
lemma regularSubgroupFiberOrbitClass_eq_iff_quotientGroup_mk_eq
    [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      QuotientGroup.mk (s := H) φ⁻¹ = QuotientGroup.mk (s := H) ψ⁻¹ := by
  constructor
  · intro h
    have h' := congrArg
      (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e) h
    rw [regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul] at h'
    exact h'
  · intro h
    apply (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).injective
    rw [regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]
    exact h

end Deck

end TauCeti
