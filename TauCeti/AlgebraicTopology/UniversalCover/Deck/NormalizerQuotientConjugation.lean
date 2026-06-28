/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotientConjugation
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation

/-!
# Conjugating deck normalizer quotients

An isomorphism of covers over a common base identifies deck groups by conjugation. This file
records the induced identification on the normalizer quotients `N(H) / H` of deck subgroups.
Those quotients are the algebraic groups appearing in the universal-covers roadmap as deck
groups of covers attached to subgroups.

## Main declarations

* `TauCeti.Deck.normalizerQuotientConjEquiv`: conjugation along an over-base homeomorphism
  identifies `N(H) / H` with `N(conj(H)) / conj(H)`.
* Representative formulas for the forward and inverse maps.

## References

This supplies a basepoint-change and cover-isomorphism bookkeeping prerequisite for
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8: pointed connected covers
correspond to subgroups, unpointed connected covers correspond to conjugacy classes of
subgroups, and the deck group attached to `H` is `N(H) / H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → B} {q : F → B}

/-- Conjugating an over-base homeomorphism identifies the normalizer quotient of a deck
subgroup with the normalizer quotient of the conjugated subgroup. -/
@[expose] noncomputable def normalizerQuotientConjEquiv (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :=
  Subgroup.normalizerQuotientEquivMap H (conjMulEquiv h hpq)

/-- On normalizer representatives, the deck normalizer-quotient conjugation equivalence is
induced by conjugating deck transformations. -/
@[simp]
lemma normalizerQuotientConjEquiv_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ) =
      Subgroup.normalizerQuotientMk
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (Subgroup.normalizerEquivMap H (conjMulEquiv h hpq) φ) :=
  Subgroup.normalizerQuotientEquivMap_mk H (conjMulEquiv h hpq) φ

/-- The inverse deck normalizer-quotient conjugation equivalence is induced by inverse
conjugation of deck transformations. -/
@[simp]
lemma normalizerQuotientConjEquiv_symm_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p))
    (ψ : _root_.Subgroup.normalizer
      ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :
        Set (Deck q))) :
    (normalizerQuotientConjEquiv h hpq H).symm
        (Subgroup.normalizerQuotientMk
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) ψ) =
      Subgroup.normalizerQuotientMk H
        ((Subgroup.normalizerEquivMap H (conjMulEquiv h hpq)).symm ψ) :=
  Subgroup.normalizerQuotientEquivMap_symm_mk H (conjMulEquiv h hpq) ψ

/-- On underlying deck transformations, the normalizer representative in the target quotient
is obtained by conjugation. -/
@[simp]
lemma normalizerQuotientConjEquiv_mk_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ) =
      Subgroup.normalizerQuotientMk
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        ⟨conjMulEquiv h hpq (φ : Deck p), by
          rw [← Subgroup.normalizerEquivMap_apply_coe H (conjMulEquiv h hpq) φ]
          exact (Subgroup.normalizerEquivMap H (conjMulEquiv h hpq) φ).2⟩ := by
  exact Subgroup.normalizerQuotientEquivMap_mk_coe H (conjMulEquiv h hpq) φ

/-- On representatives, inverse transport of the deck normalizer quotient applies inverse
conjugation. -/
@[simp]
lemma normalizerQuotientConjEquiv_symm_mk_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p))
    (ψ : _root_.Subgroup.normalizer
      ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :
        Set (Deck q))) :
    (normalizerQuotientConjEquiv h hpq H).symm
        (Subgroup.normalizerQuotientMk
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) ψ) =
      Subgroup.normalizerQuotientMk H
        ⟨(conjMulEquiv h hpq).symm (ψ : Deck q), by
          rw [← Subgroup.normalizerEquivMap_symm_apply_coe H (conjMulEquiv h hpq) ψ]
          exact ((Subgroup.normalizerEquivMap H (conjMulEquiv h hpq)).symm ψ).2⟩ := by
  rw [normalizerQuotientConjEquiv_symm_mk]
  rfl

end Deck

end TauCeti
