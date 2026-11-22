/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.RelationalConfiguration.SentenceSpectrum
import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
import TauCeti.ModelTheory.Counting.Scattered.Thin

/-!
# Sentence spectra, single-sentence splits, and scatteredness

This module specializes the configuration-level sentence-spectrum and split results of
`TauCeti.ModelTheory.RelationalConfiguration.SentenceSpectrum` to `IsThinOnNatModels`,
`BFScattered`, `ConcentratedAtBFLevels`, and `countableModelCount`:

1. **Sentence-spectrum characterizations on `ℕ`.** In a countable relational vocabulary, an
   infinitary sentence `φ` with countable branching is thin on `ℕ` if and only if every countable
   sequence `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on
   `modelsOf (V := ℕ) φ` (`isThinOnNatModels_iff_countable_image_sentenceTheory`), and similarly a
   Borel set `K` on `ℕ` is back-and-forth scattered if and only if every countable sequence realizes
   only countably many truth sequences on `K` (`bfScattered_iff_countable_image_sentenceTheory`).
2. **Single-sentence splits.** Every `L_{ω₁ω}` sentence cut with a countable side forces
   scatteredness (`bfScattered_of_measurableSet_of_sentence_splits`) and concentration
   (`concentratedAtBFLevels_of_measurableSet_of_sentence_splits`); for `L_{ω₁ω}` model classes on
   `ℕ`, concentration at all countable back-and-forth levels is equivalent to every single-sentence
   cut having a side with countably many models up to isomorphism
   (`concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`). Analogous cuts
   force `IsThinOnNatModels` (`isThinOnNatModels_of_holds_splits`,
   `isThinOnNatModels_of_countable_quotient_inf_or_not`) and forbid perfectly many countable models
   (`not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`).

## Main results

* `TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory` and
  `TauCeti.bfScattered_iff_countable_image_sentenceTheory`: sentence-spectrum characterizations of
  thin sentences and Borel scattered sets on `ℕ`.
* `TauCeti.bfScattered_of_measurableSet_of_sentence_splits`,
  `TauCeti.concentratedAtBFLevels_of_measurableSet_of_sentence_splits`, and
  `TauCeti.concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`:
  scatteredness and concentration from single-sentence countable splits.
* `TauCeti.isThinOnNatModels_of_holds_splits`,
  `TauCeti.isThinOnNatModels_of_countable_quotient_inf_or_not`, and
  `TauCeti.not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`: thinness on `ℕ`
  and absence of perfectly many countable models from single-sentence splits.

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

universe u v uι uκ

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

/-! ### Sentence-spectrum characterizations on `ℕ` -/

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

/-- If every countable `L_{ω₁ω}` sentence sequence realizes countably many truth sequences on
`modelsOf (V := ℕ) φ`, then `φ` is thin on `ℕ`. No countability hypothesis on the branching index
`κ` of `φ` is needed. -/
theorem isThinOnNatModels_of_countable_image_sentenceTheory {φ : L.SentenceInf κ}
    (h : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_of_forall_countable_image_sentenceTheory h)

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

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}

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
  simp only [isoSetoidOn, Setoid.countable_quotient_comap_val_iff, modelsOf_inf, modelsOf_not,
    ← sdiff_eq] at hθ
  exact hθ

/-- **Single-sentence splits force thinness on `ℕ`.** If `classOf : modelsOf (V := ℕ) φ → Q`
carries a satisfaction predicate `holds` agreeing with `modelsOf` for `L_{ω₁ω}` sentences, and
every `L_{ω₁ω}` sentence holds or fails on only countably many points of `Q`, then `φ` is thin on
`ℕ`. -/
theorem isThinOnNatModels_of_holds_splits [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} {Q : Type*} (classOf : modelsOf (V := ℕ) φ → Q)
    (holds : L.Sentenceω → Q → Prop)
    (hholds : ∀ (θ : L.Sentenceω) (c : modelsOf (V := ℕ) φ),
      c.val ∈ modelsOf θ ↔ holds θ (classOf c))
    (hsplit : ∀ θ : L.Sentenceω, {q : Q | holds θ q}.Countable ∨ {q : Q | ¬ holds θ q}.Countable) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_of_holds_splits classOf holds hholds hsplit)

/-- **Thinness on `ℕ` from `φ ⊓ θ` / `φ ⊓ θ.not` isomorphism-class splits.** In a countable
relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not` has
countably many models on `ℕ` up to isomorphism, then `φ` is thin on `ℕ`. -/
theorem isThinOnNatModels_of_countable_quotient_inf_or_not [∀ n, Countable (L.Relations n)]
    {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not)))) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2
    (RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not h)

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
  · exact isThinOnNatModels_of_countable_quotient_inf_or_not fun θ =>
      (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).1)
        (fun hle => (countableModelCount_le_aleph0_iff.1 hle).1)
  · exact RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not fun θ =>
      (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)
        (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)

end Splits

end TauCeti
