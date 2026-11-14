/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.Thin
public import TauCeti.ModelTheory.RelationalConfiguration.SentenceSpectrum
import TauCeti.Data.Setoid.Countable

/-!
# Sentence spectra, thin sentences, and smooth model classes

Combining the `L_{ω₁ω}` sentence-spectrum theory on `RelationalConfiguration L V`
(`TauCeti.RelationalConfiguration.isThinOn_iff_countable_image_sentenceTheory`,
`TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`) with the
equivalence between thinness and back-and-forth scatteredness on `ℕ`
(`TauCeti.bfScattered_modelsOf_iff_isThinOnNatModels`) connects syntactic `L_{ω₁ω}` invariants
directly to model counting:

* A Borel set `K` of configurations on `ℕ` is back-and-forth scattered if and only if every
  countable sequence of `L_{ω₁ω}` sentences realizes only countably many truth-value patterns on `K`
  (`TauCeti.bfScattered_iff_countable_image_sentenceTheory`).
* An infinitary sentence `φ` with countable branching is thin on `ℕ` (equivalently back-and-forth
  scattered on `ℕ`) if and only if every countable `L_{ω₁ω}` sentence sequence has countable image
  on `modelsOf (V := ℕ) φ` (`TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory`,
  `TauCeti.bfScattered_modelsOf_iff_countable_image_sentenceTheory`).
* If every single `L_{ω₁ω}` sentence `θ` splits `φ` into `φ ⊓ θ` and `φ ⊓ θ.not` with at least one
  side having countably many models up to isomorphism, then `φ` is thin (and scattered on `ℕ`), and
  when the split holds for total countable model counts `countableModelCount`, `φ` has no perfect
  set of pairwise non-isomorphic countable models at any tier
  (`TauCeti.isThinOnNatModels_of_countable_quotient_inf_or_not`,
  `TauCeti.not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`).
* Isomorphism `isoSetoidOn V φ` on the models of `φ` over a countable carrier `V` is smooth if and
  only if some countable sequence of `L_{ω₁ω}` sentences is a complete isomorphism invariant on
  `modelsOf (V := V) φ`
  (`TauCeti.RelationalConfiguration.isSmooth_isoSetoidOn_iff_exists_sentenceTheory`), and smoothness
  forces countably many isomorphism classes on `ℕ` whenever `φ` is thin on `ℕ`
  (`TauCeti.IsThinOnNatModels.countable_quotient_isoSetoidOn_of_isSmooth`).

## Main results

* `TauCeti.bfScattered_iff_countable_image_sentenceTheory`: Borel back-and-forth scattered sets on
  `ℕ` are characterized by countability of all countable `L_{ω₁ω}` sentence spectra.
* `TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory` and
  `TauCeti.bfScattered_modelsOf_iff_countable_image_sentenceTheory`: sentence-spectrum
  characterizations of `IsThinOnNatModels` and `BFScattered (modelsOf φ)`.
* `TauCeti.RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not`,
  `TauCeti.isThinOnNatModels_of_countable_quotient_inf_or_not`, and
  `TauCeti.not_hasPerfectlyManyCountableModels_of_countableModelCount_inf_or_not`: thinness from
  single-sentence `φ ⊓ θ` / `φ ⊓ θ.not` splits with a countable side.
* `TauCeti.RelationalConfiguration.isSmooth_isoSetoidOn_iff_exists_sentenceTheory`: smoothness of
  `isoSetoidOn V φ` as classification by a countable `L_{ω₁ω}` sentence spectrum.
* `TauCeti.IsThinOnNatModels.countable_quotient_isoSetoidOn_of_isSmooth` and
  `TauCeti.IsThinOnNatModels.countable_quotient_isoSetoidOn_of_countablySeparated`: thin sentences
  with smooth isomorphism (or a Borel complete invariant into a countably separated space) have
  countably many models on `ℕ` up to isomorphism.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), 894–914.
* S. Gao, *Invariant Descriptive Set Theory*, Pure and Applied Mathematics 293, CRC Press, 2009,
  §11.3 and Chapter 12.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
* Related specializations to sentences on `ℕ` appear in
  `InfinitaryLogic/Descriptive/ThinSentenceSpectra.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0); here the results also cover finite carriers via `countableModelCount` and connect
  Borel complete invariants directly to `Setoid.IsSmooth` on `isoSetoidOn`.
-/

public section

universe u v w uι uι'

open FirstOrder FirstOrder.Language Cardinal MeasurableSpace Set

namespace TauCeti

namespace RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι} {ι' : Type uι'}

/-- **Single-sentence `φ ⊓ θ` / `φ ⊓ θ.not` cuts force thinness.** On a countable carrier `V` in a
countable relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not`
has countably many models on `V` up to isomorphism, then `modelsOf (V := V) φ` is thin for
isomorphism. -/
theorem isThinOn_modelsOf_of_countable_quotient_inf_or_not
    [∀ n, Countable (L.Relations n)] [Countable V] {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      Countable (Quotient (isoSetoidOn V (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn V (φ ⊓ θ.not)))) :
    (isoSetoid L V).IsThinOn (modelsOf (V := V) φ) := by
  refine isThinOn_of_countable_image_quotientMk_inter_or_diff fun θ => ?_
  rcases h θ with hpos | hneg
  · left
    rw [← modelsOf_inf]
    exact Setoid.countable_quotient_comap_val_iff.1 hpos
  · right
    rw [sdiff_eq, ← modelsOf_not, ← modelsOf_inf]
    exact Setoid.countable_quotient_comap_val_iff.1 hneg

/-- Any countable sequence of countable-branching sentences that is a complete isomorphism invariant
on `modelsOf (V := V) φ` makes `isoSetoidOn V φ` smooth. -/
theorem isSmooth_isoSetoidOn_of_sentenceTheory [Countable ι'] [Countable V] {φ : L.SentenceInf ι}
    {θ : ℕ → L.SentenceInf ι'}
    (hsep : ∀ ⦃c⦄, c ∈ modelsOf (V := V) φ → ∀ ⦃d⦄, d ∈ modelsOf (V := V) φ →
      (isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d)) :
    (isoSetoidOn V φ).IsSmooth :=
  isSmooth_comap_isoSetoid_of_sentenceTheory hsep

/-- **Smoothness of `isoSetoidOn V φ` via `L_{ω₁ω}` sentence spectra.** On a countable carrier `V`
in a countable relational vocabulary, isomorphism on the models of a countable-branching sentence
`φ` is smooth if and only if some sequence `θ : ℕ → L.Sentenceω` is a complete isomorphism invariant
on `modelsOf (V := V) φ`. -/
theorem isSmooth_isoSetoidOn_iff_exists_sentenceTheory
    [∀ n, Countable (L.Relations n)] [Countable ι] [Countable V] (φ : L.SentenceInf ι) :
    (isoSetoidOn V φ).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω,
        ∀ ⦃c⦄, c ∈ modelsOf (V := V) φ → ∀ ⦃d⦄, d ∈ modelsOf (V := V) φ →
          (isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d) :=
  isSmooth_comap_isoSetoid_iff_exists_sentenceTheory (measurableSet_modelsOf φ)

/-- Any measurable complete isomorphism invariant on `modelsOf (V := V) φ` into a countably
separated measurable space makes `isoSetoidOn V φ` smooth. -/
theorem isSmooth_isoSetoidOn_of_countablySeparated {φ : L.SentenceInf ι} {Y : Type*}
    [MeasurableSpace Y] [CountablySeparated Y] {g : modelsOf (V := V) φ → Y} (hg : Measurable g)
    (hsep : ∀ c d : modelsOf (V := V) φ, isoSetoid L V c.1 d.1 ↔ g c = g d) :
    (isoSetoidOn V φ).IsSmooth :=
  isSmooth_comap_isoSetoid_of_countablySeparated hg hsep

end RelationalConfiguration

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}

/-! ### Sentence spectra of scattered sets and thin sentences -/

/-- **Sentence-spectrum characterization of Borel scattered sets.** In a countable relational
vocabulary, a Borel set `K` of configurations on `ℕ` is back-and-forth scattered if and only if
every countable sequence of `L_{ω₁ω}` sentences takes countably many truth-value patterns on `K`. -/
theorem bfScattered_iff_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K) :
    BFScattered K ↔ ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' K).Countable :=
  ⟨fun h => (isThinOn_iff_countable_image_sentenceTheory hK).1 h.isThinOn,
    fun h => BFScattered.of_isThinOn hK (isThinOn_of_countable_image_sentenceTheory h)⟩

/-- If every countable `L_{ω₁ω}` sentence sequence realizes countably many truth-value patterns on
`modelsOf (V := ℕ) φ`, then `φ` is thin on `ℕ`. No countability hypothesis on the branching index
`ι` of `φ` is needed. -/
theorem isThinOnNatModels_of_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι}
    (h : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_of_countable_image_sentenceTheory h)

/-- A thin countable-branching sentence realizes only countably many truth-value patterns on `ℕ`
along any countable sequence of `L_{ω₁ω}` sentences. -/
theorem IsThinOnNatModels.countable_image_sentenceTheory [∀ n, Countable (L.Relations n)]
    [Countable ι] {φ : L.SentenceInf ι} (h : IsThinOnNatModels φ) (θ : ℕ → L.Sentenceω) :
    (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  countable_image_sentenceTheory_of_isThinOn (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.1 h) θ

/-- **Sentence-spectrum characterization of thin sentences.** For an infinitary sentence with
countable branching in a countable relational vocabulary, `φ` is thin on `ℕ` if and only if every
countable sequence of `L_{ω₁ω}` sentences takes countably many truth-value patterns on
`modelsOf (V := ℕ) φ`. -/
theorem isThinOnNatModels_iff_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)]
    [Countable ι] {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  ⟨IsThinOnNatModels.countable_image_sentenceTheory,
    isThinOnNatModels_of_countable_image_sentenceTheory⟩

/-- **Sentence-spectrum characterization of scattered model classes.** For an infinitary sentence
with countable branching in a countable relational vocabulary, `modelsOf (V := ℕ) φ` is
back-and-forth scattered if and only if every countable `L_{ω₁ω}` sentence sequence has countable
image on `modelsOf (V := ℕ) φ`. -/
theorem bfScattered_modelsOf_iff_countable_image_sentenceTheory [∀ n, Countable (L.Relations n)]
    [Countable ι] {φ : L.SentenceInf ι} :
    BFScattered (modelsOf (V := ℕ) φ) ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  bfScattered_modelsOf_iff_isThinOnNatModels.trans
    isThinOnNatModels_iff_countable_image_sentenceTheory

/-! ### Single-sentence splits -/

/-- **Single-sentence splits force thinness on `ℕ`.** If `classOf : modelsOf (V := ℕ) φ → Q` carries
a satisfaction predicate `sat` agreeing with `modelsOf` for `L_{ω₁ω}` sentences, and every `L_{ω₁ω}`
sentence splits `Set.range classOf` with at least one countable side, then `φ` is thin on `ℕ`. -/
theorem isThinOnNatModels_of_sentence_splits [∀ n, Countable (L.Relations n)]
    {φ : L.SentenceInf ι} {Q : Type*} (classOf : modelsOf (V := ℕ) φ → Q)
    (sat : L.Sentenceω → Q → Prop)
    (hsat : ∀ (c : modelsOf (V := ℕ) φ) (θ : L.Sentenceω),
      c.1 ∈ modelsOf θ ↔ sat θ (classOf c))
    (hsplit : ∀ θ : L.Sentenceω,
      {q ∈ range classOf | sat θ q}.Countable ∨ {q ∈ range classOf | ¬ sat θ q}.Countable) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_of_sentence_splits classOf sat hsat hsplit)

/-- **Thinness on `ℕ` from `φ ⊓ θ` / `φ ⊓ θ.not` isomorphism-class splits.** In a countable
relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not` has
countably many models on `ℕ` up to isomorphism, then `φ` is thin on `ℕ`. -/
theorem isThinOnNatModels_of_countable_quotient_inf_or_not [∀ n, Countable (L.Relations n)]
    {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not)))) :
    IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (isThinOn_modelsOf_of_countable_quotient_inf_or_not h)

/-- In a countable relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or
`φ ⊓ θ.not` has countably many models on `ℕ` up to isomorphism, then `modelsOf (V := ℕ) φ` is
back-and-forth scattered. -/
theorem bfScattered_modelsOf_of_countable_quotient_inf_or_not [∀ n, Countable (L.Relations n)]
    {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not)))) :
    BFScattered (modelsOf (V := ℕ) φ) :=
  (isThinOnNatModels_of_countable_quotient_inf_or_not h).bfScattered_modelsOf

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
  · exact isThinOn_modelsOf_of_countable_quotient_inf_or_not fun θ =>
      (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)
        (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)

/-! ### Smoothness and thinness -/

/-- **Thin sentences with smooth isomorphism have countably many models on `ℕ`.** In a countable
relational vocabulary, if a countable-branching sentence `φ` is thin on `ℕ` and `isoSetoidOn ℕ φ`
is smooth, then `φ` has countably many models on `ℕ` up to isomorphism. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_of_isSmooth
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) (hsmooth : (isoSetoidOn ℕ φ).IsSmooth) :
    Countable (Quotient (isoSetoidOn ℕ φ)) :=
  countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.1 h) hsmooth

/-- A thin countable-branching sentence admitting a measurable complete isomorphism invariant on
`modelsOf (V := ℕ) φ` into a countably separated measurable space has countably many models on `ℕ`
up to isomorphism. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_of_countablySeparated
    [∀ n, Countable (L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) {Y : Type*} [MeasurableSpace Y] [CountablySeparated Y]
    {g : modelsOf (V := ℕ) φ → Y} (hg : Measurable g)
    (hsep : ∀ c d : modelsOf (V := ℕ) φ, isoSetoid L ℕ c.1 d.1 ↔ g c = g d) :
    Countable (Quotient (isoSetoidOn ℕ φ)) :=
  countable_quotient_comap_isoSetoid_of_isThinOn_of_countablySeparated (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.1 h) hg hsep

end TauCeti
