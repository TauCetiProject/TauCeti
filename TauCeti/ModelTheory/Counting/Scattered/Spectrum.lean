/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Spectrum
import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
import TauCeti.ModelTheory.Counting.Scattered.Thin

/-!
# Sentence spectra, single-sentence splits, and scatteredness

This module specializes the configuration-level sentence-spectrum and split results of
`TauCeti.ModelTheory.RelationalConfiguration.Sentence.Spectrum` to `BFScattered` and
`ConcentratedAtBFLevels`:

1. **Sentence-spectrum characterization on `ℕ`.** In a countable relational vocabulary, a Borel
   set `K` on `ℕ` is back-and-forth scattered if and only if every countable sequence
   `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on `K`
   (`bfScattered_iff_countable_image_sentenceTheory`).
2. **Single-sentence splits.** Every `L_{ω₁ω}` sentence cut with a countable side forces
   scatteredness (`bfScattered_of_measurableSet_of_sentence_splits`) and concentration
   (`concentratedAtBFLevels_of_measurableSet_of_sentence_splits`); for `L_{ω₁ω}` model classes on
   `ℕ`, concentration at all countable back-and-forth levels is equivalent to every single-sentence
   cut having a side with countably many models up to isomorphism
   (`concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`).

## Main results

* `TauCeti.bfScattered_iff_countable_image_sentenceTheory`: sentence-spectrum characterization of
  Borel scattered sets on `ℕ`.
* `TauCeti.bfScattered_of_measurableSet_of_sentence_splits`,
  `TauCeti.concentratedAtBFLevels_of_measurableSet_of_sentence_splits`, and
  `TauCeti.concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`:
  scatteredness and concentration from single-sentence countable splits.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* M. Morley, *The number of countable models*, Journal of Symbolic Logic **35** (1970), 14–18.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapters 4–5.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University Press,
  2021, Part 2, Chapter XII.
-/

public section

universe u v

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

/-! ### Sentence-spectrum characterization of Borel scattered sets on `ℕ` -/

section ThinSpectrum

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **Sentence-spectrum characterization of Borel scattered sets.** In a countable relational
vocabulary, a Borel set `K` of configurations on `ℕ` is back-and-forth scattered if and only if
every countable sequence of `L_{ω₁ω}` sentences realizes only countably many truth sequences on
`K`. -/
theorem bfScattered_iff_countable_image_sentenceTheory {K : Set (RelationalConfiguration L ℕ)}
    (hK : MeasurableSet K) :
    BFScattered K ↔ ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' K).Countable :=
  ⟨fun h => (isThinOn_iff_countable_image_sentenceTheory hK).1 h.isThinOn,
    fun h => BFScattered.of_isThinOn hK (isThinOn_of_forall_countable_image_sentenceTheory h)⟩

end ThinSpectrum

/-! ### Single-sentence countable splits -/

section Splits

variable {L : Language.{u, v}} [L.IsRelational]

/-- On `ℕ`, any Borel set whose every `L_{ω₁ω}` sentence cut has a side meeting only countably many
isomorphism classes is back-and-forth scattered. -/
theorem bfScattered_of_measurableSet_of_sentence_splits [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K)
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable) :
    BFScattered K :=
  BFScattered.of_isThinOn hK (isThinOn_of_sentence_splits hsplit)

/-- On `ℕ`, any Borel set whose every `L_{ω₁ω}` sentence cut has a side meeting only countably many
isomorphism classes is concentrated at all countable back-and-forth levels. -/
theorem concentratedAtBFLevels_of_measurableSet_of_sentence_splits [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K)
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits
    (bfScattered_of_measurableSet_of_sentence_splits hK hsplit) hsplit

/-- **Sentence-cut characterization of concentrated `L_{ω₁ω}` model classes on `ℕ`.** In a countable
relational vocabulary, `modelsOf (V := ℕ) φ` is concentrated at all countable back-and-forth levels
if and only if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not` has only countably
many models on `ℕ` up to isomorphism. -/
theorem concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn
    [∀ n, Countable (L.Relations n)] {φ : L.Sentenceω} :
    ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ↔
      ∀ θ : L.Sentenceω,
        Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
          Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not))) := by
  refine ⟨fun hφ θ => hφ.countable_quotient_isoSetoidOn_inf_or_inf_not θ, fun hsplit => ?_⟩
  refine concentratedAtBFLevels_of_measurableSet_of_sentence_splits (measurableSet_modelsOf φ)
    fun θ => ?_
  have hθ := hsplit θ
  simp only [isoSetoidOn, classIso, Setoid.countable_quotient_comap_val_iff, modelsOf_inf,
    modelsOf_not, ← sdiff_eq] at hθ
  exact hθ

end Splits

end TauCeti
