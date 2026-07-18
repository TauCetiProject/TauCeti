/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic

/-!
# Fibres of connected covers as deck torsors

For a preconnected covering map, a nonempty fibre on which the deck group acts
pretransitively is a principal homogeneous space for the deck group. This packages the local
form of the simply transitive fibre action; regular covers specialize it by supplying
pretransitivity on every fibre.

The torsor structure is bookkeeping needed by the universal-covers roadmap Stage 2, where
pointed covers and unpointed covers differ by changing a chosen lift of the basepoint.

## Main declarations

* `TauCeti.Deck.fiberTorsorOfPretransitive`: a nonempty pretransitive fibre of a
  preconnected cover is a `Torsor (Deck p)`.
* `TauCeti.Deck.fiber_sdiv_eq_deckEquivFiberOfSurjective_symm`: fibre division is computed
  by the inverse of the local deck-to-fibre equivalence.
* `TauCeti.Deck.deckEquivFiberOfSurjective_symm_eq_sdiv`: the same characterization in the
  simp direction from old local equivalence API to torsor division.

## References

This supplies a small prerequisite for the regular-cover and pointed/unpointed-cover
bookkeeping in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2. It builds on the connected
deck-action API in `TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic` and Mathlib's
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

/-- In the local fibre torsor, `e₁ /ₛ e₂` is the inverse local equivalence from `e₂` applied
to `e₁`. -/
lemma fiber_sdiv_eq_deckEquivFiberOfSurjective_symm [PreconnectedSpace E]
    (hp : IsCoveringMap p)
    [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})]
    (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsorOfPretransitive hp b
    e₁ /ₛ e₂ =
      (deckEquivFiberOfSurjective hp e₂ (MulAction.surjective_smul (Deck p) e₂)).symm e₁ :=
by
  rfl

/-- In the local fibre torsor, the inverse of `deckEquivFiberOfSurjective` computes the
quotient of a point by the chosen base point. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_eq_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})]
    (e e' : p ⁻¹' {b}) :
    letI := fiberTorsorOfPretransitive hp b
    (deckEquivFiberOfSurjective hp e (MulAction.surjective_smul (Deck p) e)).symm e' =
      e' /ₛ e := by
  rw [fiber_sdiv_eq_deckEquivFiberOfSurjective_symm hp]

end Deck

end TauCeti
