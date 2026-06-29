/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.RegularTorsor

/-!
# Transporting deck fibre torsors

An over-base homeomorphism between two covers identifies their deck groups by conjugation
and their corresponding fibres by `Deck.fiberMap`. This file records that these two
identifications are compatible with the torsor structures on fibres.

The main statement is first proved for the local situation of a preconnected covering whose
chosen fibre has a free transitive deck action. The regular-cover wrappers then specialize
it using `Deck.IsRegular`, which is the form used in the universal-covers roadmap when
pointed covers are compared up to changing representatives over the same base.

## Main declarations

* `TauCeti.Deck.fiberMap_sdiv_eq_conjMulEquiv_of_pretransitive`: fibre transport carries
  torsor division to conjugation of the corresponding deck transformation.
* `TauCeti.Deck.fiberMap_sdiv_eq_conjMulEquiv`: the regular-cover specialization.
* `TauCeti.Deck.deckEquivFiber_fiberMap`: transport is compatible with the
  deck-to-fibre equivalence of a regular cover.

## References

This supplies a bookkeeping prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 2: the pointed and unpointed cover correspondences require changing the chosen lift in
a fibre while transporting deck actions along isomorphisms of covers.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} {b : B}

/-- Fibre transport preserves torsor division, with the deck-group element transported by
conjugation along the over-base homeomorphism.

This is the local pretransitive-fibre form. The regular-cover API below supplies the
nonemptiness and pretransitivity hypotheses from `Deck.IsRegular`. -/
@[simp]
lemma fiberMap_sdiv_eq_conjMulEquiv_of_pretransitive [PreconnectedSpace E]
    [PreconnectedSpace F] (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})]
    [Nonempty (q ⁻¹' {b})] [MulAction.IsPretransitive (Deck q) (q ⁻¹' {b})]
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsorOfPretransitive hp b
    letI := fiberTorsorOfPretransitive hq b
    (fiberMap h hpq b e₁ /ₛ fiberMap h hpq b e₂ : Deck q) =
      conjMulEquiv h hpq (e₁ /ₛ e₂ : Deck p) := by
  letI := fiberTorsorOfPretransitive hp b
  letI := fiberTorsorOfPretransitive hq b
  rw [← deckEquivFiberOfSurjective_symm_eq_sdiv hq,
    ← deckEquivFiberOfSurjective_symm_eq_sdiv hp]
  apply eq_of_fiber_smul_eq_fiber_smul hq
  calc
    ((deckEquivFiberOfSurjective hq (fiberMap h hpq b e₂)
          (MulAction.surjective_smul (Deck q) (fiberMap h hpq b e₂))).symm
        (fiberMap h hpq b e₁)) • fiberMap h hpq b e₂ =
        fiberMap h hpq b e₁ := by
      exact deckEquivFiberOfSurjective_symm_smul hq (fiberMap h hpq b e₂)
        (MulAction.surjective_smul (Deck q) (fiberMap h hpq b e₂))
        (fiberMap h hpq b e₁)
    _ = fiberMap h hpq b
        (((deckEquivFiberOfSurjective hp e₂
            (MulAction.surjective_smul (Deck p) e₂)).symm e₁) • e₂) := by
      rw [deckEquivFiberOfSurjective_symm_smul]
    _ = conjMulEquiv h hpq
          ((deckEquivFiberOfSurjective hp e₂
            (MulAction.surjective_smul (Deck p) e₂)).symm e₁) •
        fiberMap h hpq b e₂ := by
      rw [fiberMap_smul]

/-- For regular preconnected covers, fibre transport preserves torsor division, with the
deck transformation conjugated to the target deck group. -/
@[simp]
lemma fiberMap_sdiv_eq_conjMulEquiv [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    letI := fiberTorsor hq (hreg.conj h hpq) b
    (fiberMap h hpq b e₁ /ₛ fiberMap h hpq b e₂ : Deck q) =
      conjMulEquiv h hpq (e₁ /ₛ e₂ : Deck p) := by
  let hregq := hreg.conj h hpq
  letI := hreg.nonempty_fiber b
  letI := hreg.fiber_isPretransitive b
  letI := hregq.nonempty_fiber b
  letI := hregq.fiber_isPretransitive b
  exact fiberMap_sdiv_eq_conjMulEquiv_of_pretransitive hp hq h hpq e₁ e₂

/-- The inverse of the local deck-to-fibre equivalence is compatible with fibre transport:
transport the target fibre point first, or compute the source deck transformation first and
then conjugate it. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_fiberMap [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e e' : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e)
    (hsurjq : Function.Surjective fun ψ : Deck q => ψ • fiberMap h hpq b e) :
    (deckEquivFiberOfSurjective hq (fiberMap h hpq b e) hsurjq).symm
        (fiberMap h hpq b e') =
      conjMulEquiv h hpq ((deckEquivFiberOfSurjective hp e hsurj).symm e') := by
  apply (deckEquivFiberOfSurjective hq (fiberMap h hpq b e) hsurjq).injective
  rw [Equiv.apply_symm_apply, deckEquivFiberOfSurjective_apply, ← fiberMap_smul,
    deckEquivFiberOfSurjective_symm_smul]

/-- The local deck-to-fibre equivalence commutes with transport of deck transformations
and fibre points along an over-base homeomorphism. -/
@[simp]
lemma deckEquivFiberOfSurjective_fiberMap [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e)
    (hsurjq : Function.Surjective fun ψ : Deck q => ψ • fiberMap h hpq b e) (φ : Deck p) :
    deckEquivFiberOfSurjective hq (fiberMap h hpq b e) hsurjq (conjMulEquiv h hpq φ) =
      fiberMap h hpq b (deckEquivFiberOfSurjective hp e hsurj φ) := by
  rw [deckEquivFiberOfSurjective_apply, deckEquivFiberOfSurjective_apply, fiberMap_smul]

/-- On underlying points, local compatibility of `deckEquivFiberOfSurjective` with fibre
transport says that conjugating a deck transformation and then evaluating on the transported
fibre point is the same as transporting the original evaluation. -/
@[simp]
lemma deckEquivFiberOfSurjective_fiberMap_coe [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e)
    (hsurjq : Function.Surjective fun ψ : Deck q => ψ • fiberMap h hpq b e) (φ : Deck p) :
    (deckEquivFiberOfSurjective hq (fiberMap h hpq b e) hsurjq
        (conjMulEquiv h hpq φ) : F) =
      h (φ.1 e.1) := by
  rw [deckEquivFiberOfSurjective_fiberMap hp hq h hpq e hsurj hsurjq φ,
    fiberMap_apply_coe, deckEquivFiberOfSurjective_apply_coe]

/-- The inverse of the regular deck-to-fibre equivalence is compatible with fibre transport:
transport the target fibre point first, or compute the source deck transformation first and
then conjugate it. -/
@[simp]
lemma deckEquivFiber_symm_fiberMap [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e e' : p ⁻¹' {b}) :
    (deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e)).symm
        (fiberMap h hpq b e') =
      conjMulEquiv h hpq ((deckEquivFiber hp hreg e).symm e') := by
  let hregq := hreg.conj h hpq
  letI := hreg.fiber_isPretransitive b
  letI := hregq.fiber_isPretransitive b
  exact deckEquivFiberOfSurjective_symm_fiberMap hp hq h hpq e e'
    (MulAction.surjective_smul (Deck p) e)
    (MulAction.surjective_smul (Deck q) (fiberMap h hpq b e))

/-- The regular deck-to-fibre equivalence commutes with transport of deck transformations
and fibre points along an over-base homeomorphism. -/
@[simp]
lemma deckEquivFiber_fiberMap [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) (φ : Deck p) :
    deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e) (conjMulEquiv h hpq φ) =
      fiberMap h hpq b (deckEquivFiber hp hreg e φ) := by
  let hregq := hreg.conj h hpq
  letI := hreg.fiber_isPretransitive b
  letI := hregq.fiber_isPretransitive b
  exact deckEquivFiberOfSurjective_fiberMap hp hq h hpq e
    (MulAction.surjective_smul (Deck p) e)
    (MulAction.surjective_smul (Deck q) (fiberMap h hpq b e)) φ

/-- On underlying points, the compatibility of `deckEquivFiber` with fibre transport says
that conjugating a deck transformation and then evaluating on the transported fibre point is
the same as transporting the original evaluation. -/
@[simp]
lemma deckEquivFiber_fiberMap_coe [PreconnectedSpace E] [PreconnectedSpace F]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) (φ : Deck p) :
    (deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e)
        (conjMulEquiv h hpq φ) : F) =
      h (φ.1 e.1) := by
  rw [deckEquivFiber_fiberMap hp hq hreg h hpq e φ, fiberMap_apply_coe,
    deckEquivFiber_apply_coe]

end Deck

end TauCeti
