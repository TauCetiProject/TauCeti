/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Basic
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

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup`: identifies
  `SubgroupFiberOrbitQuotient H b` with `Deck p ⧸ H`.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivQuotientGroup`: the regular-cover
  specialization that installs the free-transitive deck action on the fibre.
* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE`: compatibility with
  the maps induced by subgroup inclusions.

## References

This supplies a prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, items
7 and 8, especially the regular-cover milestones comparing fibre quotients with the
normalizer quotient `N(H)/H`. It is a deck-specific specialization of Mathlib's
`MulAction.equivSubgroupOrbitsQuotientGroup`, the orbit-quotient form of the
orbit-stabilizer theorem for free transitive actions.
-/

public section

namespace TauCeti

namespace MulAction

/-- Mathlib's subgroup-orbit quotient equivalence sends the coset of `g` back to the orbit
class of `g⁻¹ • x`. This exposes that representative convention once, so later lemmas can
rewrite through a named theorem rather than relying directly on definitional equality. -/
private lemma equivSubgroupOrbitsQuotientGroup_symm_mk
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [IsCancelSMul G X] (H : Subgroup G) (x : X) (g : G) :
    (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
        (QuotientGroup.mk (s := H) g) =
      (Quotient.mk'' (g⁻¹ • x) : MulAction.orbitRel.Quotient H X) :=
  rfl

/-- The subgroup-orbit quotient equivalence sends the orbit class of `g • x` to the coset
of `g⁻¹`. -/
private lemma equivSubgroupOrbitsQuotientGroup_apply_smul
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [IsCancelSMul G X] (H : Subgroup G) (x : X) (g : G) :
    MulAction.equivSubgroupOrbitsQuotientGroup x H
        (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
      QuotientGroup.mk (s := H) g⁻¹ := by
  simpa [equivSubgroupOrbitsQuotientGroup_symm_mk, inv_inv] using
    (MulAction.equivSubgroupOrbitsQuotientGroup x H).apply_symm_apply
    (QuotientGroup.mk (s := H) g⁻¹)

/-- `Setoid.map_of_le` sends a representative of the smaller orbit relation to the same
representative for the larger orbit relation. -/
private lemma orbitRel_mapOfLE_mk
    {G X : Type*} [Group G] [MulAction G X] {H K : Subgroup G} (hHK : H ≤ K) (x : X) :
    Setoid.map_of_le
        (_root_.TauCeti.MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      (Quotient.mk'' x : MulAction.orbitRel.Quotient K X) :=
  rfl

/-- The subgroup-orbit quotient equivalence is natural in subgroup inclusions. -/
@[simp]
private lemma equivSubgroupOrbitsQuotientGroup_mapOfLE
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [IsCancelSMul G X] {H K : Subgroup G} (hHK : H ≤ K) (x₀ : X)
    (x : MulAction.orbitRel.Quotient H X) :
    Subgroup.quotientMapOfLE hHK
        (MulAction.equivSubgroupOrbitsQuotientGroup x₀ H x) =
      MulAction.equivSubgroupOrbitsQuotientGroup x₀ K
        (Setoid.map_of_le
          (_root_.TauCeti.MulAction.orbitRel_le_of_subgroup_le (G := G) (X := X) hHK) x) := by
  refine Quotient.inductionOn' x ?_
  intro x'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ x'
  rw [← hg]
  rw [equivSubgroupOrbitsQuotientGroup_apply_smul]
  rw [orbitRel_mapOfLE_mk hHK]
  rw [equivSubgroupOrbitsQuotientGroup_apply_smul, Subgroup.quotientMapOfLE_apply_mk]

end MulAction

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- The subgroup-fibre orbit quotient is equivalent to the quotient of the deck group by the
subgroup, once the deck action on the chosen fibre is free and transitive. -/
noncomputable def subgroupFiberOrbitQuotientEquivQuotientGroup
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H :=
  MulAction.equivSubgroupOrbitsQuotientGroup e H

/-- For a regular preconnected covering map, the subgroup-fibre orbit quotient is equivalent
to the quotient of the deck group by the subgroup. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivQuotientGroup
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H :=
  @subgroupFiberOrbitQuotientEquivQuotientGroup E B _ p b
    (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H e

/-- The inverse quotient equivalence sends the coset of a deck transformation `φ` to the
`H`-orbit class of the point `φ⁻¹ • e`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  simpa [subgroupFiberOrbitQuotientEquivQuotientGroup, subgroupFiberOrbitClass_eq_mk] using
    MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk H e φ

/-- For a regular cover, the inverse quotient equivalence sends the coset of a deck
transformation `φ` to the `H`-orbit class of `φ⁻¹ • e`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]

/-- On underlying points, the inverse quotient equivalence sends the coset of `φ` to the
class of the value of `φ⁻¹` on the chosen fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm
        (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk]
  apply congrArg (subgroupFiberOrbitClass H)
  ext
  exact fiber_smul_coe φ⁻¹ e

/-- The inverse quotient equivalence sends the identity coset to the orbit class of the chosen
fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm
        (QuotientGroup.mk (s := H) (1 : Deck p)) =
      subgroupFiberOrbitClass H e := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk, inv_one, one_smul]

/-- The quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset of `φ`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  rw [← subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]
  exact (subgroupFiberOrbitQuotientEquivQuotientGroup H e).apply_symm_apply
    (QuotientGroup.mk (s := H) φ)

/-- For a regular cover, the quotient equivalence sends the orbit class of `φ⁻¹ • e` to the
coset of `φ`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa [regularSubgroupFiberOrbitQuotientEquivQuotientGroup] using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ

/-- The quotient equivalence sends the chosen fibre point to the identity coset. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : Deck p) := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e (1 : Deck p)

/-- The quotient equivalence sends the orbit class of `φ • e` to the coset of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ⁻¹

/-- For a regular cover, the quotient equivalence sends the orbit class of `φ • e` to the
coset of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa [regularSubgroupFiberOrbitQuotientEquivQuotientGroup] using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul H e φ

/-- The subgroup-fibre quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (subgroupFiberOrbitQuotientEquivQuotientGroup H e x) =
      subgroupFiberOrbitQuotientEquivQuotientGroup K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  simp [subgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitMapOfLE, MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE
      (G := Deck p) (X := p ⁻¹' {b}) hHK e x]

/-- For a regular cover, the subgroup-fibre quotient equivalence is natural in subgroup
inclusions. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE hHK e x]

/-- Equality of subgroup fibre-orbit classes is equality of the corresponding deck cosets
under the quotient equivalence, with the inverse orientation coming from Mathlib's quotient
convention. -/
lemma subgroupFiberOrbitClass_eq_iff_quotientGroup_mk_inv_eq
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      QuotientGroup.mk (s := H) φ⁻¹ = QuotientGroup.mk (s := H) ψ⁻¹ := by
  constructor
  · intro h
    have h' := congrArg
      (subgroupFiberOrbitQuotientEquivQuotientGroup H e) h
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul] at h'
    exact h'
  · intro h
    apply (subgroupFiberOrbitQuotientEquivQuotientGroup H e).injective
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]
    exact h

end Deck

end TauCeti
