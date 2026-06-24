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

* `TauCeti.Deck.fiberTorsor`: the fibre of a regular preconnected cover is a
  `Torsor (Deck p)`.
* `TauCeti.Deck.fiber_sdiv_eq`: fibre division is the unique deck transformation carrying
  the second point to the first.
* `TauCeti.Deck.deckEquivFiber_mul`: the existing equivalence `Deck p ≃ fibre` is
  equivariant for left multiplication on `Deck p` and the deck action on the fibre.
* `TauCeti.Deck.deckEquivFiber_symm_apply_smul`: the inverse equivalence is compatible with
  translating fibre points.

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

/-- The fibre of a regular preconnected covering is a torsor for its deck group.

The division `e₁ /ₛ e₂` is the unique deck transformation carrying `e₂` to `e₁`, expressed
using `deckEquivFiber` at the base point `e₂`. -/
@[expose, implicit_reducible] noncomputable def fiberTorsor [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hreg : IsRegular p) (b : B) :
    Torsor (Deck p) (p ⁻¹' {b}) where
  toMulAction := instFiberMulAction
  nonempty := hreg.nonempty_fiber b
  sdiv e₁ e₂ := (deckEquivFiber hp hreg e₂).symm e₁
  sdiv_smul' e₁ e₂ := deckEquivFiber_symm_smul hp hreg e₂ e₁
  smul_sdiv' φ e := by
    rw [Equiv.symm_apply_eq]
    rfl

/-- In the regular-cover fibre torsor, `e₁ /ₛ e₂` is the unique deck transformation sending
`e₂` to `e₁`. -/
@[simp]
lemma fiber_sdiv_eq [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e₁ /ₛ e₂ = (deckEquivFiber hp hreg e₂).symm e₁ :=
  rfl

/-- The deck transformation `e₁ /ₛ e₂` sends `e₂` to `e₁` on the fibre. -/
@[simp]
lemma fiber_sdiv_smul [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (e₁ /ₛ e₂ : Deck p) • e₂ = e₁ := by
  letI := fiberTorsor hp hreg b
  exact sdiv_smul e₁ e₂

/-- A deck transformation can be recovered as the fibre quotient of its translate of a point
by that point. -/
@[simp]
lemma fiber_smul_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (φ : Deck p) (e : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (φ • e) /ₛ e = φ := by
  letI := fiberTorsor hp hreg b
  exact smul_sdiv φ e

/-- A fibre point is a translate of another point by `φ` exactly when their torsor quotient
is `φ`. -/
lemma fiber_eq_smul_iff_sdiv_eq [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e₁ : p ⁻¹' {b}) (φ : Deck p) (e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e₁ = φ • e₂ ↔ e₁ /ₛ e₂ = φ := by
  letI := fiberTorsor hp hreg b
  exact eq_smul_iff_sdiv_eq e₁ φ e₂

/-- The equivalence from deck transformations to a fibre sends the identity to the chosen
base point. -/
@[simp]
lemma deckEquivFiber_one [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    deckEquivFiber hp hreg e 1 = e := by
  rw [deckEquivFiber_apply, one_smul]

/-- The equivalence from deck transformations to a fibre is equivariant for left
multiplication on the deck group and the deck action on the fibre. -/
@[simp]
lemma deckEquivFiber_mul [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    deckEquivFiber hp hreg e (φ * ψ) = φ • deckEquivFiber hp hreg e ψ := by
  rw [deckEquivFiber_apply, deckEquivFiber_apply, mul_smul]

/-- In the regular-cover fibre torsor, the inverse of `deckEquivFiber` computes the quotient
of a point by the chosen base point. -/
@[simp]
lemma deckEquivFiber_symm_eq_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (deckEquivFiber hp hreg e).symm e' = e' /ₛ e :=
  rfl

/-- Translating a fibre point before applying the inverse `deckEquivFiber` multiplies the
corresponding deck transformation on the left. -/
@[simp]
lemma deckEquivFiber_symm_apply_smul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) (φ : Deck p) :
    (deckEquivFiber hp hreg e).symm (φ • e') =
      φ * (deckEquivFiber hp hreg e).symm e' := by
  apply (deckEquivFiber hp hreg e).injective
  rw [Equiv.apply_symm_apply, deckEquivFiber_mul, Equiv.apply_symm_apply]

/-- The quotient of two points in a regular-cover fibre is characterized by its value on the
second point. -/
lemma fiber_sdiv_eq_iff [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e₁ e₂ : p ⁻¹' {b}) (φ : Deck p) :
    letI := fiberTorsor hp hreg b
    e₁ /ₛ e₂ = φ ↔ e₁ = φ • e₂ := by
  letI := fiberTorsor hp hreg b
  exact (fiber_eq_smul_iff_sdiv_eq hp hreg e₁ φ e₂).symm

/-- The quotient of a point by itself in a regular-cover fibre is the identity deck
transformation. -/
@[simp]
lemma fiber_sdiv_self [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e /ₛ e = (1 : Deck p) := by
  letI := fiberTorsor hp hreg b
  exact sdiv_self e

/-- Fibre quotients compose as expected in the regular-cover torsor. -/
lemma fiber_sdiv_mul_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e₁ e₂ e₃ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (e₁ /ₛ e₂ : Deck p) * (e₂ /ₛ e₃) = e₁ /ₛ e₃ := by
  letI := fiberTorsor hp hreg b
  exact sdiv_mul_sdiv_cancel e₁ e₂ e₃

end Deck

end TauCeti
