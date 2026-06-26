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

* `MulAction.equivSubgroupOrbitsQuotientGroup`: applied to the deck action on one fibre, this
  identifies `SubgroupFiberOrbitQuotient H b` with `Deck p ⧸ H`.
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

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- Mathlib's subgroup-orbit quotient equivalence sends the coset of `g` back to the orbit
class of `g⁻¹ • x`. This exposes that representative convention once, so deck-facing lemmas
can rewrite through a named theorem rather than relying directly on definitional equality. -/
private lemma mulAction_equivSubgroupOrbitsQuotientGroup_symm_mk
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [IsCancelSMul G X] (H : Subgroup G) (x : X) (g : G) :
    (MulAction.equivSubgroupOrbitsQuotientGroup x H).symm
        (QuotientGroup.mk (s := H) g) =
      (Quotient.mk'' (g⁻¹ • x) : MulAction.orbitRel.Quotient H X) :=
  rfl

/-- The inverse quotient equivalence sends the coset of a deck transformation `φ` to the
`H`-orbit class of the point `φ⁻¹ • e`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (MulAction.equivSubgroupOrbitsQuotientGroup e H).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  simpa [subgroupFiberOrbitClass_eq_mk] using
    mulAction_equivSubgroupOrbitsQuotientGroup_symm_mk H e φ

/-- The regular-cover quotient equivalence sends the coset of a deck transformation `φ` back
to the `H`-orbit class of `φ⁻¹ • e`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (@MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp

/-- On underlying points, the inverse quotient equivalence sends the coset of `φ` to the
class of the value of `φ⁻¹` on the chosen fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (MulAction.equivSubgroupOrbitsQuotientGroup e H).symm
        (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk]
  congr 1

/-- On underlying points, the regular-cover inverse quotient equivalence sends the coset of
`φ` to the class of the value of `φ⁻¹` on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (@MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H).symm
        (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa using subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe H e φ

/-- The inverse quotient equivalence sends the identity coset to the orbit class of the chosen
fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (MulAction.equivSubgroupOrbitsQuotientGroup e H).symm
        (QuotientGroup.mk (s := H) (1 : Deck p)) =
      subgroupFiberOrbitClass H e := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk, inv_one, one_smul]

/-- The regular-cover inverse quotient equivalence sends the identity coset to the orbit class
of the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (@MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H).symm
        (QuotientGroup.mk (s := H) (1 : Deck p)) =
      subgroupFiberOrbitClass H e := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp

/-- The quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset of `φ`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    MulAction.equivSubgroupOrbitsQuotientGroup e H
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  rw [← subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]
  exact (MulAction.equivSubgroupOrbitsQuotientGroup e H).apply_symm_apply
    (QuotientGroup.mk (s := H) φ)

/-- The regular-cover quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset
of `φ`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    @MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa using subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ

/-- The quotient equivalence sends the chosen fibre point to the identity coset. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    MulAction.equivSubgroupOrbitsQuotientGroup e H
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : Deck p) := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e (1 : Deck p)

/-- The regular-cover quotient equivalence sends the chosen fibre point to the identity
coset. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    @MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : Deck p) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa using subgroupFiberOrbitQuotientEquivQuotientGroup_apply_base H e

/-- The quotient equivalence sends the orbit class of `φ • e` to the coset of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    MulAction.equivSubgroupOrbitsQuotientGroup e H
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ⁻¹

/-- The regular-cover quotient equivalence sends the orbit class of `φ • e` to the coset of
`φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    @MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simpa using subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul H e φ

/-- The subgroup-fibre quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (MulAction.equivSubgroupOrbitsQuotientGroup e H x) =
      MulAction.equivSubgroupOrbitsQuotientGroup e K
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ]
  rw [← subgroupFiberOrbitClass_eq_mk H (φ • e)]
  rw [subgroupFiberOrbitMapOfLE_apply,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    Subgroup.quotientMapOfLE_apply_mk]

/-- On representatives, naturality sends the class of `φ • e` through the coset map induced by
`H ≤ K`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (φ : Deck p) :
    Subgroup.quotientMapOfLE hHK
        (MulAction.equivSubgroupOrbitsQuotientGroup e H
          (subgroupFiberOrbitClass H (φ • e))) =
      MulAction.equivSubgroupOrbitsQuotientGroup e K
        (subgroupFiberOrbitMapOfLE (b := b) hHK
          (subgroupFiberOrbitClass H (φ • e))) := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE]

/-- The regular-cover subgroup-fibre quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b})
    (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (@MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
          (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H x) =
      @MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) K
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp

/-- On representatives, the regular-cover naturality lemma sends the class of `φ • e` through
the coset map induced by `H ≤ K`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (φ : Deck p) :
    Subgroup.quotientMapOfLE hHK
        (@MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
          (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H
          (subgroupFiberOrbitClass H (φ • e))) =
      @MulAction.equivSubgroupOrbitsQuotientGroup (Deck p) (p ⁻¹' {b}) _ _ e
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) K
        (subgroupFiberOrbitMapOfLE (b := b) hHK
          (subgroupFiberOrbitClass H (φ • e))) := by
  simp

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
      (MulAction.equivSubgroupOrbitsQuotientGroup e H) h
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul] at h'
    exact h'
  · intro h
    apply (MulAction.equivSubgroupOrbitsQuotientGroup e H).injective
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]
    exact h

/-- Equality of subgroup fibre-orbit classes is equality of the corresponding deck cosets
under the regular-cover quotient equivalence, with the inverse orientation coming from
Mathlib's quotient convention. -/
lemma regularSubgroupFiberOrbitClass_eq_iff_quotientGroup_mk_inv_eq
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      QuotientGroup.mk (s := H) φ⁻¹ = QuotientGroup.mk (s := H) ψ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitClass_eq_iff_quotientGroup_mk_inv_eq H e φ ψ

end Deck

end TauCeti
