/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Sentence.Basic
public import TauCeti.SetTheory.Descriptive.Antichain
import TauCeti.Basic.Countable.Basic
import TauCeti.Data.Set.Countable
import TauCeti.Data.Setoid.Countable
import TauCeti.ModelTheory.RelationalConfiguration.Observables
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Sentence-spectrum characterization of thinness and single-sentence splits

On a countable carrier `V` in a countable relational vocabulary, this module characterizes
descriptive-set-theoretic thinness of a Borel set `C : Set (RelationalConfiguration L V)` for
isomorphism in terms of `L_{ω₁ω}` sentence truth sequences (`sentenceTheory`):

1. **Sentence-spectrum characterization of thinness.** A Borel set `C` is thin for isomorphism
   (`(isoSetoid L V).IsThinOn C`) if and only if every countable sequence `θ : ℕ → L.Sentenceω`
   realizes only countably many truth sequences on `C`
   (`isThinOn_iff_countable_image_sentenceTheory`). The reverse implication
   (`isThinOn_of_forall_countable_image_sentenceTheory`) requires neither measurability nor
   isomorphism invariance of `C`.
2. **Single-sentence splits.** If `classOf : C → Q` presents `C` so that truth of `L_{ω₁ω}`
   sentences factors through `classOf` and every single sentence has a truth side meeting only
   countably many points of `Q`, then every countable sentence list realizes countably many truth
   sequences on `C` and hence `C` is thin (`isThinOn_of_splits_along`, `isThinOn_of_holds_splits`,
   `isThinOn_of_sentence_splits`, and `isThinOn_modelsOf_of_countable_quotient_inf_or_not`). Neither
   measurability nor isomorphism invariance of `C`, nor any topology, σ-algebra, or surjectivity on
   `Q`, is assumed.

## Main results

* `TauCeti.RelationalConfiguration.isThinOn_iff_countable_image_sentenceTheory`: thinness of a
  Borel configuration set via countable `L_{ω₁ω}` sentence spectra.
* `TauCeti.RelationalConfiguration.isThinOn_of_splits_along`,
  `TauCeti.RelationalConfiguration.isThinOn_of_holds_splits`,
  `TauCeti.RelationalConfiguration.isThinOn_of_sentence_splits`, and
  `TauCeti.RelationalConfiguration.isThinOn_modelsOf_of_countable_quotient_inf_or_not`: thinness
  from single-sentence countable splits.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae **57** (1965), 253–272.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Chapters 4–5.
* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
-/

public section

universe u v w uι uκ

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

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
  let F : Setoid C := Setoid.ker g
  have hF_meas : MeasurableSet {p : C × C | F p.1 p.2} :=
    (measurableSet_setOf_sentenceTheory_eq θ).preimage
      (measurable_subtypeVal.prodMap measurable_subtypeVal)
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
  let classOf : C → Quotient (isoSetoid L V) := Quot.mk _ ∘ Subtype.val
  refine isThinOn_of_splits_along classOf
    (fun c d hcd φ => (isomorphismInvariant_modelsOf φ).mem_iff (Quotient.exact hcd)) fun θ => ?_
  have hpos : classOf '' {c : C | c.val ∈ modelsOf θ} =
      Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ) := by
    change (Quotient.mk (isoSetoid L V) ∘ Subtype.val) '' (Subtype.val ⁻¹' modelsOf θ) = _
    rw [Set.image_comp, Subtype.image_preimage_val]
  have hneg : classOf '' {c : C | c.val ∉ modelsOf θ} =
      Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ) := by
    change (Quotient.mk (isoSetoid L V) ∘ Subtype.val) '' (Subtype.val ⁻¹' (modelsOf θ)ᶜ) = _
    rw [Set.image_comp, Subtype.image_preimage_val, ← Set.sdiff_eq]
  rw [hpos, hneg]
  exact hsplit θ

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
  refine isThinOn_of_sentence_splits fun θ => ?_
  simpa only [isoSetoidOn, classIso, Setoid.countable_quotient_comap_val_iff, modelsOf_inf,
    modelsOf_not, ← Set.sdiff_eq] using h θ

end Splits

end TauCeti.RelationalConfiguration
