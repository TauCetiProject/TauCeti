/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit.Basic

/-!
# Subgroup fibre orbits of a regular cover as deck-group quotients

For a regular preconnected covering map, evaluation at any point of a fibre identifies the
deck group with that fibre. This file records the corresponding quotient-level statement:
orbits of a subgroup `H ≤ deck p` on the fibre are equivalent to the coset quotient
`deck p ⧸ H`.

The classification of connected covers uses fibre quotients by subgroups, while the regular-cover
computation of the deck group of the cover attached to `H` is expressed algebraically as a
normalizer quotient. The bridge here lets arguments move between those fibre-orbit quotients and
subgroup quotients without unfolding either construction.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup`: identifies
  `SubgroupFiberOrbitQuotient H b` with `deck p ⧸ H`.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivQuotientGroup`: the regular-cover
  specialization that installs the free-transitive deck action on the fibre.
* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE`: compatibility with
  the maps induced by subgroup inclusions.
* `TauCeti.Deck.subgroupFiberOrbitQuotientBotEquivDeck`: for `H = ⊥`, the quotient is the
  deck group, with the inverse orientation coming from Mathlib's quotient convention.
* Endpoint collapse lemmas for `H = ⊤`.

## References

It is a deck-specific specialization of Mathlib's
`MulAction.equivSubgroupOrbitsQuotientGroup`, the orbit-quotient form of the
orbit-stabilizer theorem for free transitive actions.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

private lemma quotientGroup_quotientBot_mk (φ : deck p) :
    QuotientGroup.quotientBot (G := deck p)
        (QuotientGroup.mk (s := (⊥ : Subgroup (deck p))) φ) =
      φ :=
  rfl

/-- The subgroup-fibre orbit quotient is equivalent to the quotient of the deck group by the
subgroup, once the deck action on the chosen fibre is free and transitive. -/
noncomputable def subgroupFiberOrbitQuotientEquivQuotientGroup
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ deck p ⧸ H :=
  MulAction.equivSubgroupOrbitsQuotientGroup e H

/-- For a regular preconnected covering map, the subgroup-fibre orbit quotient is equivalent
to the quotient of the deck group by the subgroup. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivQuotientGroup
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ deck p ⧸ H :=
  @subgroupFiberOrbitQuotientEquivQuotientGroup E B _ p b
    (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H e

/-- The inverse quotient equivalence sends the coset of a deck transformation `φ` to the
`H`-orbit class of the point `φ⁻¹ • e`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  simp [subgroupFiberOrbitQuotientEquivQuotientGroup, subgroupFiberOrbitClass_eq_mk,
    MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk H e φ]

/-- For a regular cover, the inverse quotient equivalence sends the coset of a deck
transformation `φ` to the `H`-orbit class of `φ⁻¹ • e`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]

/-- On underlying points, the inverse quotient equivalence sends the coset of `φ` to the
class of the value of `φ⁻¹` on the chosen fibre point. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (deck.map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk]
  apply congrArg (subgroupFiberOrbitClass H)
  ext
  exact deck.fiber_smul_coe φ⁻¹ e

/-- The inverse quotient equivalence sends the identity coset to the orbit class of the chosen
fibre point. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm
        (QuotientGroup.mk (s := H) (1 : deck p)) =
      subgroupFiberOrbitClass H e := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk, inv_one, one_smul]

/-- The quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset of `φ`. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  rw [← subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]
  exact (subgroupFiberOrbitQuotientEquivQuotientGroup H e).apply_symm_apply
    (QuotientGroup.mk (s := H) φ)

/-- For a regular cover, the quotient equivalence sends the orbit class of `φ⁻¹ • e` to the
coset of `φ`. -/
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp only [regularSubgroupFiberOrbitQuotientEquivQuotientGroup]
  exact subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ

/-- The quotient equivalence sends the chosen fibre point to the identity coset. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : deck p) := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e (1 : deck p)

/-- The quotient equivalence sends the orbit class of `φ • e` to the coset of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
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
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ : deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup]

/-- For a free transitive deck action on a fibre, quotienting the fibre by the trivial
subgroup identifies that quotient with the deck group. The representative convention is the
same as `subgroupFiberOrbitQuotientEquivQuotientGroup`: the class of `φ • e` corresponds to
`φ⁻¹`. -/
noncomputable def subgroupFiberOrbitQuotientBotEquivDeck
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (deck p)) b ≃ deck p :=
  (subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (deck p)) e).trans
    (QuotientGroup.quotientBot (G := deck p) : deck p ⧸ (⊥ : Subgroup (deck p)) ≃ deck p)

/-- For a regular preconnected covering map, the quotient of a fibre by the trivial deck
subgroup is the deck group. -/
noncomputable def regularSubgroupFiberOrbitQuotientBotEquivDeck
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (deck p)) b ≃ deck p :=
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  subgroupFiberOrbitQuotientBotEquivDeck e

/-- The bottom-subgroup quotient-to-deck equivalence sends the class of `φ • e` to `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_apply_smul
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : deck p) :
    subgroupFiberOrbitQuotientBotEquivDeck e
        (subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) (φ • e)) =
      φ⁻¹ := by
  have h := congrArg (QuotientGroup.quotientBot (G := deck p))
    (subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
      (H := (⊥ : Subgroup (deck p))) e φ)
  simpa [subgroupFiberOrbitQuotientBotEquivDeck] using h.trans (quotientGroup_quotientBot_mk φ⁻¹)

/-- For a regular cover, the bottom-subgroup quotient-to-deck equivalence sends the class of
`φ • e` to `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : deck p) :
    regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e
        (subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) (φ • e)) =
      φ⁻¹ := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitQuotientBotEquivDeck_apply_smul e φ

/-- The chosen fibre point maps to the identity deck transformation under the
bottom-subgroup quotient-to-deck equivalence. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_apply_base
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientBotEquivDeck e
        (subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) e) =
      1 := by
  simpa using subgroupFiberOrbitQuotientBotEquivDeck_apply_smul e (1 : deck p)

/-- For a regular cover, the chosen fibre point maps to the identity deck transformation
under the bottom-subgroup quotient-to-deck equivalence. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_base
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e
        (subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) e) =
      1 := by
  simpa using
    regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_smul hp hreg e (1 : deck p)

/-- The inverse bottom-subgroup quotient-to-deck equivalence sends a deck transformation to
the class of its inverse acting on the chosen fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_symm_apply
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : deck p) : (subgroupFiberOrbitQuotientBotEquivDeck e).symm φ =
      subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) (φ⁻¹ • e) := by
  apply (subgroupFiberOrbitQuotientBotEquivDeck e).injective
  rw [Equiv.apply_symm_apply, subgroupFiberOrbitQuotientBotEquivDeck_apply_smul]
  simp

/-- For a regular cover, the inverse bottom-subgroup quotient-to-deck equivalence sends a
deck transformation to the class of its inverse acting on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_symm_apply
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : deck p) :
    (regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e).symm φ =
      subgroupFiberOrbitClass (⊥ : Subgroup (deck p)) (φ⁻¹ • e) := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientBotEquivDeck]

/-- Under the quotient-group equivalence, the full-subgroup fibre quotient lands in the
unique coset of `deck p ⧸ ⊤`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_top
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient (⊤ : Subgroup (deck p)) b) :
    subgroupFiberOrbitQuotientEquivQuotientGroup (⊤ : Subgroup (deck p)) e x =
      QuotientGroup.mk (s := (⊤ : Subgroup (deck p))) (1 : deck p) := by
  have := QuotientGroup.subsingleton_quotient_top (G := deck p)
  exact Subsingleton.elim _ _

/-- For a regular cover, the full-subgroup fibre quotient lands in the unique coset of
`deck p ⧸ ⊤`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_top
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient (⊤ : Subgroup (deck p)) b) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg (⊤ : Subgroup (deck p)) e x =
      QuotientGroup.mk (s := (⊤ : Subgroup (deck p))) (1 : deck p) := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_top e x]

/-- The subgroup-fibre quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    {H K : Subgroup (deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (subgroupFiberOrbitQuotientEquivQuotientGroup H e x) =
      subgroupFiberOrbitQuotientEquivQuotientGroup K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  simp [subgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitMapOfLE, MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE
      (G := deck p) (X := p ⁻¹' {b}) hHK e x]

/-- For a regular cover, the subgroup-fibre quotient equivalence is natural in subgroup
inclusions. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    {H K : Subgroup (deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  let := hreg.fiber_isPretransitive b
  let := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE hHK e x]

/-- Equality of subgroup fibre-orbit classes is equality of the corresponding deck cosets
under the quotient equivalence, with the inverse orientation coming from Mathlib's quotient
convention. -/
lemma subgroupFiberOrbitClass_eq_iff_quotientGroup_mk_inv_eq
    [MulAction.IsPretransitive (deck p) (p ⁻¹' {b})] [IsCancelSMul (deck p) (p ⁻¹' {b})]
    (H : Subgroup (deck p)) (e : p ⁻¹' {b}) (φ ψ : deck p) :
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
