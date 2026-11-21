/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Torsor
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic

/-!
# Fibres of regular connected covers as deck torsors

For a preconnected covering map with regular deck action, evaluation at any point of a fibre
identifies the deck group with that fibre. This file packages the same fact in the standard
Mathlib language of torsors: the fibre is a principal homogeneous space for the deck group.

Pointed covers and unpointed covers differ by changing a chosen lift of the basepoint, and
regular covers are characterized by transitivity of the deck action on fibres; the torsor
structure keeps track of both.

## Main declarations

* `TauCeti.Deck.fiberTorsor`: the regular-cover specialization.
* `TauCeti.Deck.fiber_sdiv_eq_deckEquivFiber_symm`: fibre division is the unique deck
  transformation carrying the second point to the first.
* `TauCeti.Deck.addActionOfMulEquiv`, `TauCeti.Deck.fiberAddTorsorOfMulEquiv`: an isomorphism
  `Multiplicative A ≃* deck p` makes the additive group `A` act on the total space, and each
  fibre of a regular preconnected covering an `A`-torsor.

## References

It specializes the local torsor API in
`TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Torsor` using the regular deck-action
API in `TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

/-- The fibre of a regular preconnected covering is a torsor for its deck group. -/
@[reducible]
noncomputable def fiberTorsor [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hreg : IsRegular p) (b : B) :
    Torsor (deck p) (p ⁻¹' {b}) := by
  letI := hreg.nonempty_fiber b
  letI := hreg.fiber_isPretransitive b
  exact fiberTorsorOfPretransitive hp b

/-- In the regular-cover fibre torsor, `e₁ /ₛ e₂` is the inverse equivalence from `e₂`
applied to `e₁`. -/
lemma fiber_sdiv_eq_deckEquivFiber_symm [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e₁ /ₛ e₂ = (deckEquivFiber hp hreg e₂).symm e₁ :=
by
  let := hreg.nonempty_fiber b
  let := hreg.fiber_isPretransitive b
  exact fiber_sdiv_eq_deckEquivFiberOfSurjective_symm hp e₁ e₂

/-- In the regular-cover fibre torsor, the inverse of `deckEquivFiber` computes the quotient
of a point by the chosen base point. -/
@[simp]
lemma deckEquivFiber_symm_eq_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (deckEquivFiber hp hreg e).symm e' = e' /ₛ e := by
  rw [fiber_sdiv_eq_deckEquivFiber_symm hp hreg]

section OfMulEquiv

variable {A : Type*} [AddGroup A]

/-- An isomorphism `Multiplicative A ≃* deck p` makes the additive group `A` act on the total
space: `a` acts by the deck transformation labelled by `a`. -/
@[reducible]
noncomputable def addActionOfMulEquiv (φ : Multiplicative A ≃* deck p) : AddAction A E :=
  AddAction.compHom E (MonoidHom.toAdditiveRight φ.toMonoidHom)

omit [TopologicalSpace B] in
/-- In `addActionOfMulEquiv φ`, the element `a` acts by the deck transformation `φ a`. -/
lemma addActionOfMulEquiv_vadd (φ : Multiplicative A ≃* deck p) (a : A) (e : E) :
    letI := addActionOfMulEquiv φ
    a +ᵥ e = (φ (Multiplicative.ofAdd a)).val e :=
  deck.smul_eq_apply (φ (Multiplicative.ofAdd a)) e

omit [TopologicalSpace B] in
/-- The action `addActionOfMulEquiv φ` preserves the projection. -/
lemma proj_addActionOfMulEquiv_vadd (φ : Multiplicative A ≃* deck p) (a : A) (e : E) :
    letI := addActionOfMulEquiv φ
    p (a +ᵥ e) = p e :=
  deck.proj_smul (φ (Multiplicative.ofAdd a)) e

/-- An isomorphism `Multiplicative A ≃* deck p` makes each fibre of a regular preconnected
covering a torsor for the additive group `A`: `a` acts by the deck transformation labelled by
`a`, and `e₁ -ᵥ e₂` is the label of the unique deck transformation carrying `e₂` to `e₁`. -/
@[reducible]
noncomputable def fiberAddTorsorOfMulEquiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (φ : Multiplicative A ≃* deck p) (b : B) : AddTorsor A (p ⁻¹' {b}) :=
  { AddAction.compHom (p ⁻¹' {b}) (MonoidHom.toAdditiveRight φ.toMonoidHom) with
    vsub e₁ e₂ := Multiplicative.toAdd (φ.symm ((deckEquivFiber hp hreg e₂).symm e₁))
    nonempty := hreg.nonempty_fiber b
    vsub_vadd' e₁ e₂ := by
      simp [AddAction.compHom_vadd_def, -deckEquivFiber_symm_eq_sdiv, deckEquivFiber_symm_smul]
    vadd_vsub' a e := by
      simp [AddAction.compHom_vadd_def, -deckEquivFiber_symm_eq_sdiv,
        deckEquivFiber_symm_apply_smul,
        (Equiv.symm_apply_eq _).2 (deckEquivFiber_one hp hreg e).symm] }

/-- In `fiberAddTorsorOfMulEquiv`, the action on a fibre is the action
`addActionOfMulEquiv φ` on the total space. -/
lemma coe_fiberAddTorsorOfMulEquiv_vadd [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (φ : Multiplicative A ≃* deck p) (a : A) (e : p ⁻¹' {b}) :
    letI := fiberAddTorsorOfMulEquiv hp hreg φ b
    letI := addActionOfMulEquiv φ
    ((a +ᵥ e : p ⁻¹' {b}) : E) = a +ᵥ (e : E) :=
  (deck.fiber_smul_coe (φ (Multiplicative.ofAdd a)) e).trans
    (addActionOfMulEquiv_vadd φ a e.val).symm

/-- In `fiberAddTorsorOfMulEquiv`, `e₁ -ᵥ e₂` labels the deck transformation carrying `e₂` to
`e₁`. -/
lemma fiberAddTorsorOfMulEquiv_vsub [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (φ : Multiplicative A ≃* deck p) (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberAddTorsorOfMulEquiv hp hreg φ b
    e₁ -ᵥ e₂ = Multiplicative.toAdd (φ.symm ((deckEquivFiber hp hreg e₂).symm e₁)) :=
  (rfl)

end OfMulEquiv

end Deck

end TauCeti
