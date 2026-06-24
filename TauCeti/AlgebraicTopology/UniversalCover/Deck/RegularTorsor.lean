/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular

/-!
# Fibres of regular connected covers as deck torsors

For a preconnected covering map with regular deck action, evaluation at any point of a fibre
identifies the deck group with that fibre. This file packages the same fact in the standard
Mathlib language of torsors: the fibre is a principal homogeneous space for the deck group.

The torsor structure is bookkeeping needed by the universal-covers roadmap Stage 2, where
pointed covers and unpointed covers differ by changing a chosen lift of the basepoint, and
regular covers are characterized by transitivity of the deck action on fibres.

## Main declarations

* `TauCeti.Deck.fiberTorsorOfPretransitive`: a nonempty pretransitive fibre of a
  preconnected cover is a `Torsor (Deck p)`.
* `TauCeti.Deck.fiberTorsor`: the regular-cover specialization.
* `TauCeti.Deck.fiber_sdiv_eq`: fibre division is the unique deck transformation carrying
  the second point to the first.

## References

This supplies a small prerequisite for the regular-cover and pointed/unpointed-cover
bookkeeping in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2. It builds on the regular
deck-action API in `TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular` and Mathlib's
generic torsor API (`Mathlib.Algebra.Torsor.Basic`).
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

/-- A nonempty pretransitive fibre of a preconnected covering is a torsor for its deck group.

The division `e₁ /ₛ e₂` is the unique deck transformation carrying `e₂` to `e₁`, expressed
using `deckEquivFiberOfSurjective` at the base point `e₂`. -/
@[reducible]
noncomputable def fiberTorsorOfPretransitive [PreconnectedSpace E] (hp : IsCoveringMap p)
    (b : B) [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] :
    Torsor (Deck p) (p ⁻¹' {b}) where
  toMulAction := instFiberMulAction
  nonempty := inferInstance
  sdiv e₁ e₂ :=
    (deckEquivFiberOfSurjective hp e₂ (MulAction.surjective_smul (Deck p) e₂)).symm e₁
  sdiv_smul' e₁ e₂ :=
    deckEquivFiberOfSurjective_symm_smul hp e₂ (MulAction.surjective_smul (Deck p) e₂) e₁
  smul_sdiv' φ e := by
    rw [Equiv.symm_apply_eq]
    rw [deckEquivFiberOfSurjective_apply]

/-- The fibre of a regular preconnected covering is a torsor for its deck group. -/
@[reducible]
noncomputable def fiberTorsor [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hreg : IsRegular p) (b : B) :
    Torsor (Deck p) (p ⁻¹' {b}) := by
  letI := hreg.nonempty_fiber b
  letI := hreg.fiber_isPretransitive b
  exact fiberTorsorOfPretransitive hp b

/-- In the regular-cover fibre torsor, `e₁ /ₛ e₂` is the unique deck transformation sending
`e₂` to `e₁`. -/
lemma fiber_sdiv_eq [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e₁ /ₛ e₂ = (deckEquivFiber hp hreg e₂).symm e₁ :=
by
  letI := fiberTorsor hp hreg b
  apply orbitMap_injective hp e₂
  change (e₁ /ₛ e₂ : Deck p) • e₂ = (deckEquivFiber hp hreg e₂).symm e₁ • e₂
  rw [sdiv_smul, deckEquivFiber_symm_smul]

/-- In the local fibre torsor, `e₁ /ₛ e₂` is the unique deck transformation sending
`e₂` to `e₁`. -/
lemma fiber_sdiv_eq_ofPretransitive [PreconnectedSpace E] (hp : IsCoveringMap p)
    [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})]
    (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsorOfPretransitive hp b
    e₁ /ₛ e₂ =
      (deckEquivFiberOfSurjective hp e₂ (MulAction.surjective_smul (Deck p) e₂)).symm e₁ :=
by
  letI := fiberTorsorOfPretransitive hp b
  apply orbitMap_injective hp e₂
  change (e₁ /ₛ e₂ : Deck p) • e₂ =
    (deckEquivFiberOfSurjective hp e₂ (MulAction.surjective_smul (Deck p) e₂)).symm e₁ • e₂
  rw [sdiv_smul, deckEquivFiberOfSurjective_symm_smul]

/-- In the regular-cover fibre torsor, the inverse of `deckEquivFiber` computes the quotient
of a point by the chosen base point. -/
@[simp]
lemma deckEquivFiber_symm_eq_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (deckEquivFiber hp hreg e).symm e' = e' /ₛ e := by
  rw [fiber_sdiv_eq hp hreg]

end Deck

end TauCeti
