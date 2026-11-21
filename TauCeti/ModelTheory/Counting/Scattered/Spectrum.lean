/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory
public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.Data.Set.Countable
import TauCeti.Logic.Countable
import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
import TauCeti.ModelTheory.Counting.Scattered.Thin
import TauCeti.ModelTheory.RelationalConfiguration.Observables
import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Sentence spectra, single-sentence splits, and thinness

This module characterizes descriptive-set-theoretic thinness, single-sentence splits, and countable
quotients of Borel classes of relational configurations in terms of `L_{ω₁ω}` sentence truth
sequences (`TauCeti.RelationalConfiguration.sentenceTheory`):

1. **Sentence-spectrum characterization of thinness.** On a countable carrier in a countable
   relational vocabulary, a Borel set `C` is thin for isomorphism if and only if every countable
   sequence `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on `C`
   (`isThinOn_iff_countable_image_sentenceTheory`, and
   `isThinOnNatModels_iff_countable_image_sentenceTheory` for model classes on `ℕ`). The reverse
   implication (`isThinOn_of_forall_countable_image_sentenceTheory`) requires neither measurability
   nor isomorphism invariance of `C`.
2. **Single-sentence splits.** If `classOf : C → Q` presents `C` so that truth of `L_{ω₁ω}`
   sentences factors through `classOf` and every single sentence has a truth side meeting only
   countably many points of `Q`, then every countable sentence list realizes countably many truth
   sequences on `C` and hence `C` is thin (`isThinOn_of_splits_along`, `isThinOn_of_holds_splits`,
   `isThinOn_of_sentence_splits`). Neither measurability nor isomorphism invariance of `C`, nor any
   topology, σ-algebra, or surjectivity on `Q`, is assumed. For `L_{ω₁ω}` model classes on `ℕ`,
   concentration at all countable back-and-forth levels is equivalent to every single-sentence cut
   having a side with countably many models up to isomorphism
   (`concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`).
3. **Countable quotients from thinness and smoothness.** On a countable carrier in a countable
   relational vocabulary, a Borel class `C` meets countably many isomorphism classes if and only if
   it is both thin for isomorphism and has smooth restricted isomorphism
   (`countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`, and
   `countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth` for model classes on
   `ℕ`).

## Main results

* `TauCeti.isThinOn_iff_countable_image_sentenceTheory` and
  `TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory`: thinness of Borel configuration
  sets and sentences via countable `L_{ω₁ω}` sentence spectra.
* `TauCeti.isThinOn_of_splits_along`, `TauCeti.isThinOn_of_holds_splits`, and
  `TauCeti.isThinOn_of_sentence_splits`: thinness from single-sentence countable splits, yielding
  `TauCeti.bfScattered_of_measurableSet_of_sentence_splits`,
  `TauCeti.concentratedAtBFLevels_of_measurableSet_of_sentence_splits`, and
  `TauCeti.concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`.
* `TauCeti.countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth`,
  `TauCeti.countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`, and
  `TauCeti.countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth`: countable
  quotients on Borel classes and model classes from thinness and smoothness.

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

universe u v w uι uκ

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

/-! ### Sentence-spectrum characterization of thinness -/

section ThinSpectrum

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {ι : Type uι} {κ : Type uκ}

/-- If every countable sequence of `L_{ω₁ω}` sentences realizes only countably many truth sequences
on `C`, then `C` carries no Cantor antichain for isomorphism. No measurability or invariance of `C`
is required. -/
theorem not_hasCantorAntichainOn_of_forall_countable_image_sentenceTheory
    {C : Set (RelationalConfiguration L V)}
    (h : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    ¬ (isoSetoid L V).HasCantorAntichainOn C := by
  intro hcantor
  obtain ⟨f, hf_cont, hfC, hf_ne⟩ := Setoid.hasCantorAntichainOn_iff.1 hcantor
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_apply_eq hf_cont.measurable hf_ne
  have huniv : (univ : Set (ℕ → Bool)).Countable :=
    (h θ).mono (by rintro x -; exact ⟨f x, hfC x, hθ x⟩)
  exact Set.not_countable_univ huniv

/-- If every countable sequence of `L_{ω₁ω}` sentences realizes only countably many truth sequences
on `C`, then `C` is thin for isomorphism. No measurability or invariance of `C` is required. -/
theorem isThinOn_of_forall_countable_image_sentenceTheory
    {C : Set (RelationalConfiguration L V)}
    (h : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    (isoSetoid L V).IsThinOn C :=
  Setoid.isThinOn_iff_not_hasCantorAntichainOn.2
    (not_hasCantorAntichainOn_of_forall_countable_image_sentenceTheory h)

/-- On a thin Borel set `C`, every countable family of infinitary sentences with countable
branching realizes only countably many truth sequences. -/
theorem countable_image_sentenceTheory_of_isThinOn [Countable ι] [Countable κ]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C) (θ : ι → L.SentenceInf κ) :
    (sentenceTheory θ '' C).Countable := by
  let g : C → ι → Bool := fun c => sentenceTheory θ c.val
  have hg : Measurable g := (measurable_sentenceTheory θ).comp measurable_subtypeVal
  let F : Setoid C := Setoid.ker g
  have hF_meas : MeasurableSet {p : C × C | F p.1 p.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd)
  have hcount : Countable (Quotient F) :=
    hthin.countable_quotient_of_measurableSet hC F
      (fun _ _ hxy => sentenceTheory_eq_of_isoSetoid hxy θ) hF_meas
  have hrange : Countable (range g) := Countable.of_equiv _ (Setoid.quotientKerEquivRange g)
  rw [Set.image_eq_range]
  exact Set.countable_coe_iff.1 hrange

/-- **Sentence-spectrum characterization of thinness.** On a countable carrier in a countable
relational vocabulary, a Borel set `C` of configurations is thin for isomorphism if and only if
every countable sequence `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on `C`.
No isomorphism invariance of `C` is assumed. -/
theorem isThinOn_iff_countable_image_sentenceTheory
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    (isoSetoid L V).IsThinOn C ↔ ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable :=
  ⟨fun hthin θ => countable_image_sentenceTheory_of_isThinOn hC hthin θ,
    isThinOn_of_forall_countable_image_sentenceTheory⟩

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

/-- **Sentence-spectrum characterization of scattered model classes.** For an infinitary sentence
with countable branching in a countable relational vocabulary, `modelsOf (V := ℕ) φ` is
back-and-forth scattered if and only if every countable `L_{ω₁ω}` sentence sequence realizes
countably many truth sequences on `modelsOf (V := ℕ) φ`. -/
theorem bfScattered_modelsOf_iff_countable_image_sentenceTheory [Countable κ]
    {φ : L.SentenceInf κ} :
    BFScattered (modelsOf (V := ℕ) φ) ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  bfScattered_modelsOf_iff_isThinOnNatModels.trans
    isThinOnNatModels_iff_countable_image_sentenceTheory

end ThinSpectrum

/-! ### Single-sentence countable splits -/

section Splits

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {ι : Type uι}

/-- If a presentation `classOf : C → Q` determines the truth of `L_{ω₁ω}` sentences on `C` and
every single sentence has a truth side meeting only countably many points of `Q`, then every
countable family `θ : ι → L.Sentenceω` realizes only countably many truth sequences on `C`. No
topology, σ-algebra, or surjectivity on `Q`, and no measurability, invariance, or vocabulary
countability on `C` or `L`, is required. -/
theorem countable_image_sentenceTheory_of_splits_along [Countable ι]
    {C : Set (RelationalConfiguration L V)} {Q : Type*} (classOf : C → Q)
    (htruth : ∀ ⦃c d : C⦄, classOf c = classOf d → ∀ φ : L.Sentenceω,
      c.val ∈ modelsOf φ ↔ d.val ∈ modelsOf φ)
    (hsplit : ∀ φ : L.Sentenceω,
      (classOf '' {c : C | c.val ∈ modelsOf φ}).Countable ∨
        (classOf '' {c : C | c.val ∉ modelsOf φ}).Countable)
    (θ : ι → L.Sentenceω) :
    (sentenceTheory θ '' C).Countable := by
  let R := range classOf
  let rep : R → C := fun q => q.property.choose
  have hrep (q : R) : classOf (rep q) = q.val := q.property.choose_spec
  let P : ι → R → Prop := fun i q => (rep q).val ∈ modelsOf (θ i)
  have hP_split (i : ι) : {q : R | P i q}.Countable ∨ {q : R | ¬ P i q}.Countable := by
    rcases hsplit (θ i) with hpos | hneg
    · refine .inl ((hpos.preimage Subtype.val_injective).mono fun q hq => ?_)
      exact ⟨rep q, hq, hrep q⟩
    · refine .inr ((hneg.preimage Subtype.val_injective).mono fun q hq => ?_)
      exact ⟨rep q, hq, hrep q⟩
  let g : R → ι → Bool := fun q => sentenceTheory θ (rep q).val
  have hg_count : (range g).Countable :=
    countable_range_of_splits g
      (fun _ _ h => sentenceTheory_eq_iff.2 h) hP_split
  refine hg_count.mono ?_
  rintro _ ⟨c, hc, rfl⟩
  let q : R := ⟨classOf ⟨c, hc⟩, mem_range_self (f := classOf) ⟨c, hc⟩⟩
  exact mem_range.2 ⟨q, sentenceTheory_eq_iff.2 fun i => htruth (hrep q) (θ i)⟩

/-- **Thinness from single-sentence splits along a presentation.** In a countable relational
vocabulary on a countable carrier, if `classOf : C → Q` determines `L_{ω₁ω}` truth on `C` and
every sentence has a truth side with countably many images in `Q`, then `C` is thin for
isomorphism. Neither measurability nor invariance of `C`, nor any structure or surjectivity on `Q`,
is assumed. -/
theorem isThinOn_of_splits_along [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} {Q : Type*} (classOf : C → Q)
    (htruth : ∀ ⦃c d : C⦄, classOf c = classOf d → ∀ φ : L.Sentenceω,
      c.val ∈ modelsOf φ ↔ d.val ∈ modelsOf φ)
    (hsplit : ∀ φ : L.Sentenceω,
      (classOf '' {c : C | c.val ∈ modelsOf φ}).Countable ∨
        (classOf '' {c : C | c.val ∉ modelsOf φ}).Countable) :
    (isoSetoid L V).IsThinOn C :=
  isThinOn_of_forall_countable_image_sentenceTheory
    (countable_image_sentenceTheory_of_splits_along classOf htruth hsplit)

/-- Presentation form with an explicit truth predicate `holds : L.Sentenceω → Q → Prop`: if truth
on `C` is read through `holds` along `classOf : C → Q` and each sentence holds or fails on only
countably many points of `Q`, then `C` is thin for isomorphism. -/
theorem isThinOn_of_holds_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} {Q : Type*}
    (classOf : C → Q) (holds : L.Sentenceω → Q → Prop)
    (hholds : ∀ (φ : L.Sentenceω) (c : C), c.val ∈ modelsOf φ ↔ holds φ (classOf c))
    (hsplit : ∀ φ : L.Sentenceω, {q : Q | holds φ q}.Countable ∨ {q : Q | ¬ holds φ q}.Countable) :
    (isoSetoid L V).IsThinOn C := by
  refine isThinOn_of_splits_along classOf
    (fun c d hcd φ => by rw [hholds φ c, hholds φ d, hcd]) fun φ => ?_
  rcases hsplit φ with hpos | hneg
  · refine .inl (hpos.mono ?_)
    rintro _ ⟨c, hc, rfl⟩
    exact (hholds φ c).1 hc
  · refine .inr (hneg.mono ?_)
    rintro _ ⟨c, hc, rfl⟩
    exact mt (hholds φ c).2 hc

/-- **Thinness from single-sentence isomorphism-class cuts.** If for every `L_{ω₁ω}` sentence `θ`
either `C ∩ modelsOf θ` or `C \ modelsOf θ` meets only countably many isomorphism classes, then `C`
is thin for isomorphism. Neither measurability nor isomorphism invariance of `C` is required. -/
theorem isThinOn_of_sentence_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)}
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ)).Countable) :
    (isoSetoid L V).IsThinOn C := by
  let classOf : C → Quotient (isoSetoid L V) := fun c => Quotient.mk (isoSetoid L V) c.val
  refine isThinOn_of_splits_along classOf
    (fun c d hcd φ => (isomorphismInvariant_modelsOf φ).mem_iff (Quotient.exact hcd)) fun θ => ?_
  have hpos : classOf '' {c : C | c.val ∈ modelsOf θ} =
      Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ) := by
    ext q
    simp only [classOf, mem_image, Subtype.exists, mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun ⟨c, hc, hθ, hq⟩ => ⟨c, ⟨hc, hθ⟩, hq⟩,
      fun ⟨c, ⟨hc, hθ⟩, hq⟩ => ⟨c, hc, hθ, hq⟩⟩
  have hneg : classOf '' {c : C | c.val ∉ modelsOf θ} =
      Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ) := by
    ext q
    simp only [classOf, mem_image, Subtype.exists, mem_ofPred_eq, mem_sdiff]
    exact ⟨fun ⟨c, hc, hθ, hq⟩ => ⟨c, ⟨hc, hθ⟩, hq⟩,
      fun ⟨c, ⟨hc, hθ⟩, hq⟩ => ⟨c, hc, hθ, hq⟩⟩
  rw [hpos, hneg]
  exact hsplit θ

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

/-- **Single-sentence `φ ⊓ θ` / `φ ⊓ θ.not` cuts force thinness.** On a countable carrier `V` in a
countable relational vocabulary, if for every `L_{ω₁ω}` sentence `θ` either `φ ⊓ θ` or `φ ⊓ θ.not`
has countably many models on `V` up to isomorphism, then `modelsOf (V := V) φ` is thin for
isomorphism. -/
theorem RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not
    [∀ n, Countable (L.Relations n)] [Countable V] {φ : L.Sentenceω}
    (h : ∀ θ : L.Sentenceω,
      Countable (Quotient (isoSetoidOn V (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn V (φ ⊓ θ.not)))) :
    (isoSetoid L V).IsThinOn (modelsOf (V := V) φ) := by
  refine isThinOn_of_sentence_splits fun θ => ?_
  simpa only [isoSetoidOn, Setoid.countable_quotient_comap_val_iff, modelsOf_inf, modelsOf_not,
    ← sdiff_eq] using h θ

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
  · exact RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not fun θ =>
      (h θ).imp (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)
        (fun hle => (countableModelCount_le_aleph0_iff.1 hle).2 n)

end Splits

/-! ### Countable quotients from thinness and smoothness -/

section Smooth

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {κ : Type uκ}

/-- **Thin smooth Borel classes have countably many isomorphism classes.** If `C` is Borel, thin
for isomorphism, and carries a Borel complete invariant (`IsSmooth`), then `C` meets only countably
many isomorphism classes. -/
theorem countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C)
    (hsmooth : ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  hthin.countable_quotient_comap_of_isSmooth hC hsmooth

/-- **Characterization of Borel classes with countably many isomorphism classes.** On a countable
carrier in a countable relational vocabulary, a Borel set `C` meets countably many isomorphism
classes if and only if `C` is thin for isomorphism and restricted isomorphism on `C` is smooth. -/
theorem countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) ↔
      (isoSetoid L V).IsThinOn C ∧ ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth := by
  refine ⟨fun hcount => ⟨?_, ?_⟩,
    fun ⟨hthin, hsmooth⟩ => countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth hC hthin
      hsmooth⟩
  · refine Setoid.isThinOn_iff_not_hasCantorAntichainOn.2 fun hcantor => ?_
    exact (aleph0_lt_continuum.trans_le hcantor.continuum_le_mk_quotient_comap).not_ge
      (mk_le_aleph0_iff.2 hcount)
  · -- Each individual isomorphism orbit is the Borel model class of its representative's Scott
    -- sentence.
    refine Setoid.isSmooth_of_countable_quotient fun x => ?_
    have horbit : {d : RelationalConfiguration L V | isoSetoid L V x.val d} =
        modelsOf (@scottSentence L _ V x.val.toStructure _ _) := by
      ext d
      exact isoSetoid_apply.trans
        ((@realize_scottSentence_iff L _ _ V x.val.toStructure _ V d.toStructure _).symm.trans
          mem_modelsOf.symm)
    exact (horbit ▸ measurableSet_modelsOf _).preimage measurable_subtypeVal

/-- An infinitary sentence `φ` with countable branching has countably many models on `ℕ` up to
isomorphism if and only if `φ` is thin on `ℕ` and `isoSetoidOn ℕ φ` is smooth. -/
theorem countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth [Countable κ]
    {φ : L.SentenceInf κ} :
    Countable (Quotient (isoSetoidOn ℕ φ)) ↔
      IsThinOnNatModels φ ∧ (isoSetoidOn ℕ φ).IsSmooth := by
  rw [isoSetoidOn, countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth
    (measurableSet_modelsOf φ), isThinOnNatModels_iff_isThinOn]

/-- **Thin sentences with smooth isomorphism have countably many models on `ℕ`.** In a countable
relational vocabulary, if a countable-branching sentence `φ` is thin on `ℕ` and `isoSetoidOn ℕ φ`
is smooth, then `φ` has countably many models on `ℕ` up to isomorphism. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_of_isSmooth [Countable κ]
    {φ : L.SentenceInf κ} (h : IsThinOnNatModels φ) (hsmooth : (isoSetoidOn ℕ φ).IsSmooth) :
    Countable (Quotient (isoSetoidOn ℕ φ)) :=
  countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth.2 ⟨h, hsmooth⟩

end Smooth

end TauCeti
