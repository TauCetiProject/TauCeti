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
all subgroups `H ≤ Deck p`. This file records the bottom-subgroup specialization: quotienting
a single fibre by the trivial subgroup gives the fibre back.

This is small bookkeeping for the universal-covers roadmap. In Stage 2, the cover associated
to a subgroup `H ≤ π₁(X, x₀)` has the universal cover as the `H = ⊥` case, while the
regular-cover computation compares subgroup fibre quotients with deck-group quotients. The
lemmas here let later arguments use that specialization without unfolding the orbit relation
or the quotient construction.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientBotEquiv`: the quotient by the trivial subgroup is
  the original fibre.
* `TauCeti.Deck.subgroupFiberOrbitClass_bot_eq_iff`: equality of bottom-subgroup classes is
  equality of fibre points.
* Compatibility lemmas with the maps induced by `⊥ ≤ H` and, under the regular-cover
  hypotheses, with the quotient-group equivalence to `Deck p ⧸ ⊥`.

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

/-- In the bottom-subgroup action on a fibre, orbit-related points are equal. -/
lemma eq_of_orbitRel_bot {e e' : p ⁻¹' {b}}
    (h : MulAction.orbitRel (⊥ : Subgroup (Deck p)) (p ⁻¹' {b}) e e') : e = e' := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨φ, hφ⟩
  have hφ_one : (φ : Deck p) = 1 := by
    exact Subgroup.mem_bot.mp φ.2
  have hsmul : (φ : Deck p) • e' = e := hφ
  rw [hφ_one, one_smul] at hsmul
  exact hsmul.symm

/-- Quotienting a fibre by the trivial deck subgroup gives the fibre itself. -/
@[expose] noncomputable def subgroupFiberOrbitQuotientBotEquiv :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b ≃ p ⁻¹' {b} where
  toFun := Quotient.lift id fun _ _ h => eq_of_orbitRel_bot h
  invFun := subgroupFiberOrbitClass (⊥ : Subgroup (Deck p))
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro e
    rfl
  right_inv := by
    intro e
    rfl

/-- The bottom-subgroup quotient equivalence sends a class to its representative fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquiv_apply (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientBotEquiv
        (p := p) (b := b) (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e) = e :=
  rfl

/-- The inverse bottom-subgroup quotient equivalence sends a fibre point to its quotient
class. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquiv_symm_apply (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm e =
      subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e :=
  rfl

/-- Equality of bottom-subgroup fibre-orbit classes is equality of fibre points. -/
@[simp]
lemma subgroupFiberOrbitClass_bot_eq_iff (e e' : p ⁻¹' {b}) :
    subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e =
        subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e' ↔
      e = e' := by
  constructor
  · intro h
    exact congrArg (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)) h
  · intro h
    rw [h]

/-- The quotient map induced by `⊥ ≤ H`, after identifying the bottom quotient with the
fibre, is the `H`-orbit class map. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_bot_apply (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitMapOfLE (b := b) (bot_le : (⊥ : Subgroup (Deck p)) ≤ H)
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm e) =
      subgroupFiberOrbitClass H e :=
  rfl

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma subgroupFiberOrbitMapOfLE_bot_eq (H : Subgroup (Deck p)) :
    subgroupFiberOrbitMapOfLE (p := p) (b := b)
        (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) =
      (fun e => subgroupFiberOrbitClass H e) ∘
        subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- Equality in an `H`-fibre quotient can be checked after choosing representatives through
the bottom quotient. -/
lemma subgroupFiberOrbitMapOfLE_bot_eq_iff (H : Subgroup (Deck p))
    (x y : SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b) :
    subgroupFiberOrbitMapOfLE (p := p) (b := b)
        (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) x =
        subgroupFiberOrbitMapOfLE (p := p) (b := b)
          (bot_le : (⊥ : Subgroup (Deck p)) ≤ H) y ↔
      subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) x ∈
        MulAction.orbit H (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) y) := by
  simpa [subgroupFiberOrbitMapOfLE_bot_eq] using
    subgroupFiberOrbitClass_eq_iff H
      (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) x)
      (subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b) y)

/-- Under the regular-cover quotient-group equivalence, the bottom-subgroup class of
`φ⁻¹ • e` corresponds to the quotient class of `φ`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_bot_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (Deck p)) e
        ((subgroupFiberOrbitQuotientBotEquiv (p := p) (b := b)).symm (φ⁻¹ • e)) =
      QuotientGroup.mk (s := (⊥ : Subgroup (Deck p))) φ := by
  rw [subgroupFiberOrbitQuotientBotEquiv_symm_apply,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul]

/-- Under the regular-cover quotient-group equivalence, the bottom-subgroup class of
`φ • e` corresponds to the quotient class of `φ⁻¹`. -/
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
