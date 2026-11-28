/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Spectrum

/-!
# Sentence spectra and single-sentence splits for countable model counting

This module specializes the configuration-level sentence-spectrum and split results of
`TauCeti.ModelTheory.RelationalConfiguration.Sentence.Spectrum` to `IsThinOnNatModels` and
`HasPerfectlyManyCountableModels`:

1. **Sentence-spectrum characterization on `ℕ`.** In a countable relational vocabulary, an
   infinitary sentence `φ` with countable branching is thin on `ℕ` if and only if every countable
   sequence `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on
   `modelsOf (V := ℕ) φ` (`isThinOnNatModels_iff_countable_image_sentenceTheory`), and any thin
   sentence realizes only countably many truth sequences for any countable family of
   countable-branching sentences (`IsThinOnNatModels.countable_image_sentenceTheory`).
2. **Single-sentence splits.** If for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not`
   has at most countably many countable models across all finite and infinite tiers, then `φ` does
   not have perfectly many countable models
   (`not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`).

## Main results

* `TauCeti.IsThinOnNatModels.countable_image_sentenceTheory` and
  `TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory`: sentence-spectrum characterization
  of thinness on `ℕ`.
* `TauCeti.not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`: absence of
  perfectly many countable models from single-sentence splits.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* M. Morley, *The number of countable models*, Journal of Symbolic Logic **35** (1970), 14–18.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapters 4–5.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
-/

public section

universe u v uι uκ

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

section ThinSpectrum

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {ι : Type uι} {κ : Type uκ}

/-- On a thin sentence's models on `ℕ`, every countable family of infinitary sentences with
countable branching realizes only countably many truth sequences. -/
theorem IsThinOnNatModels.countable_image_sentenceTheory [Countable ι] [Countable κ]
    {κ' : Type*} [Countable κ'] {φ : L.SentenceInf κ} (hφ : IsThinOnNatModels φ)
    (θ : ι → L.SentenceInf κ') :
    (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  countable_image_sentenceTheory_of_isThinOn (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.1 hφ) θ

/-- **Sentence-spectrum characterization of thin sentences.** An infinitary sentence `φ` with
countable branching is thin on `ℕ` if and only if every countable sequence of `L_{ω₁ω}` sentences
realizes only countably many truth sequences on `modelsOf (V := ℕ) φ`. -/
theorem isThinOnNatModels_iff_countable_image_sentenceTheory [Countable κ]
    {φ : L.SentenceInf κ} :
    IsThinOnNatModels φ ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable := by
  rw [isThinOnNatModels_iff_isThinOn,
    isThinOn_iff_countable_image_sentenceTheory (measurableSet_modelsOf φ)]

end ThinSpectrum

section Splits

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Single-sentence countable-model splits forbid perfectly many countable models.** In a
countable relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not`
has at most countably many countable models across all finite and infinite tiers, then `φ` does not
have perfectly many countable models. -/
theorem not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not
    [∀ n, Countable (L.Relations n)] {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      countableModelCount (φ ⊓ θ) ≤ ℵ₀ ∨ countableModelCount (φ ⊓ θ.not) ≤ ℵ₀) :
    ¬ HasPerfectlyManyCountableModels φ := by
  refine not_hasPerfectlyManyCountableModels_iff.2 ⟨?_, fun n => ?_⟩
  · exact isThinOnNatModels_iff_isThinOn.2 <|
      RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not fun θ =>
        (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).1)
          (fun hle => (countableModelCount_le_aleph0_iff.1 hle).1)
  · exact RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not fun θ =>
      (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)
        (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)

end Splits

end TauCeti
