/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Opposite
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup

/-!
# Regular covers with commutative deck group

For a regular covering map `p : E → X` with simply connected total space, Tau Ceti's
regular-cover comparison identifies the fundamental group of the base with the opposite deck
group:

  `FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`.

This file records the commutative specialization. If the deck group is commutative, the
opposite can be removed to give a direct multiplicative equivalence

  `FundamentalGroup X x ≃* Deck p`.

The accompanying lemmas mirror the monodromy characterizations in
`TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup`, so downstream applications
such as the circle covering can use the direct deck group without repeating the
opposite-removal bookkeeping.

## Main declarations

* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck`: for a simply connected regular cover
  with commutative deck group, `π₁(X, x) ≃* Deck p`.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck_smul`: the associated deck
  transformation moves the chosen lift by monodromy.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck_apply_eq_iff`: equality with a deck
  transformation is characterized by its value on the chosen lift.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck_symm_apply_eq_iff`: the same
  characterization, phrased for the inverse equivalence.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck_symm_monodromy`: the inverse
  equivalence is characterized by monodromy.
* `TauCeti.Deck.IsRegular.fundamentalGroupMulEquivDeck_eq_one_iff`: the kernel is the loop
  classes whose monodromy fixes the chosen lift.

## References

This is a small convention wrapper around `TauCeti.Deck.IsRegular.fundamentalGroupEquiv`.
It supports the UniversalCovers roadmap Stage 1 convention check and Stage 4 circle
application, where the relevant deck groups are abelian.
-/

public section

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

/-- For a regular covering map `p : E → X` with simply connected total space and commutative
deck group, the fundamental group of the base is multiplicatively equivalent to the deck
transformation group. This is `IsRegular.fundamentalGroupEquiv` with the opposite removed using
the explicit commutativity hypothesis on `Deck p`. -/
@[expose] noncomputable def IsRegular.fundamentalGroupMulEquivDeck [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ) :
    FundamentalGroup X x ≃* Deck p :=
  { toFun γ := (hreg.fundamentalGroupEquiv hp e γ).unop
    invFun φ := (hreg.fundamentalGroupEquiv hp e).symm (MulOpposite.op φ)
    left_inv γ := by simp
    right_inv φ := by simp
    map_mul' γ γ' := by
      rw [map_mul, MulOpposite.unop_mul]
      exact hcomm ((hreg.fundamentalGroupEquiv hp e γ').unop)
        ((hreg.fundamentalGroupEquiv hp e γ).unop) }

@[simp]
lemma IsRegular.fundamentalGroupMulEquivDeck_apply [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupMulEquivDeck hp e hcomm γ =
      (hreg.fundamentalGroupEquiv hp e γ).unop :=
  rfl

/-- The deck transformation attached to a loop class by
`fundamentalGroupMulEquivDeck` moves the chosen lift `e` along the monodromy of that loop. -/
@[simp]
lemma IsRegular.fundamentalGroupMulEquivDeck_smul [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupMulEquivDeck hp e hcomm γ • (e : E) =
      (hp.monodromy γ e : E) := by
  simpa using hreg.fundamentalGroupEquiv_unop_smul hp e γ

/-- The direct commutative-deck comparison sends `γ` to `φ` exactly when `φ` moves the chosen
lift `e` to the monodromy translate of `e` along `γ`. -/
lemma IsRegular.fundamentalGroupMulEquivDeck_apply_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (γ : FundamentalGroup X x) (φ : Deck p) :
    hreg.fundamentalGroupMulEquivDeck hp e hcomm γ = φ ↔
      φ • (e : E) = hp.monodromy γ e := by
  rw [fundamentalGroupMulEquivDeck_apply]
  constructor
  · intro h
    exact (hreg.fundamentalGroupEquiv_apply_eq_iff hp e γ (MulOpposite.op φ)).mp
      (by simpa using congrArg MulOpposite.op h)
  · intro h
    exact congrArg MulOpposite.unop
      ((hreg.fundamentalGroupEquiv_apply_eq_iff hp e γ (MulOpposite.op φ)).mpr h)

/-- A deck transformation corresponds to `γ` under the inverse direct commutative-deck
comparison exactly when it moves the chosen lift `e` to the monodromy translate of `e` along
`γ`. -/
lemma IsRegular.fundamentalGroupMulEquivDeck_symm_apply_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (φ : Deck p) (γ : FundamentalGroup X x) :
    (hreg.fundamentalGroupMulEquivDeck hp e hcomm).symm φ = γ ↔
      φ • (e : E) = hp.monodromy γ e := by
  rw [MulEquiv.symm_apply_eq]
  rw [eq_comm]
  exact hreg.fundamentalGroupMulEquivDeck_apply_eq_iff hp e hcomm γ φ

/-- The loop class corresponding to a deck transformation under the inverse direct
commutative-deck comparison has monodromy action equal to that deck transformation at the
chosen lift. -/
lemma IsRegular.fundamentalGroupMulEquivDeck_symm_monodromy [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (φ : Deck p) :
    (hp.monodromy ((hreg.fundamentalGroupMulEquivDeck hp e hcomm).symm φ) e : E) =
      φ • (e : E) := by
  have hsymm :
      (hreg.fundamentalGroupMulEquivDeck hp e hcomm).symm φ =
        (hreg.fundamentalGroupEquiv hp e).symm (MulOpposite.op φ) := by
    rfl
  rw [hsymm]
  exact hreg.fundamentalGroupEquiv_symm_op_monodromy hp e φ

/-- A loop class maps to the identity deck transformation under the direct commutative-deck
comparison exactly when its monodromy fixes the chosen lift. -/
@[simp]
lemma IsRegular.fundamentalGroupMulEquivDeck_eq_one_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ φ ψ : Deck p, φ * ψ = ψ * φ)
    (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupMulEquivDeck hp e hcomm γ = 1 ↔ hp.monodromy γ e = e := by
  rw [fundamentalGroupMulEquivDeck_apply]
  simpa using hreg.fundamentalGroupEquiv_eq_one_iff hp e γ

end Deck

end TauCeti
