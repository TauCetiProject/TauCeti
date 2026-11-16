/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Thin
public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
public import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory
public import TauCeti.ModelTheory.Scott.Isomorphism
public import TauCeti.SetTheory.Descriptive.BorelReducibility
public import TauCeti.Topology.MetricSpace.Polish.Pi
import TauCeti.Data.Set.Countable
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Sentence spectra, Borel observables, and thinness

This module characterizes Borel observables, descriptive-set-theoretic thinness, single-sentence
splits, and smoothness of isomorphism on relational configurations in terms of `L_{ω₁ω}` sentence
truth sequences (`TauCeti.RelationalConfiguration.sentenceTheory`):

1. **Borel observables and Cantor recovery.** Along a measurable family `f : X →
   RelationalConfiguration L V` parametrized by a standard Borel space `X`, every
   isomorphism-invariant measurable map `g : X → ι → Bool` is realized as `sentenceTheory θ ∘ f`
   for a family `θ : ι → L.Sentenceω` (`exists_sentenceTheory_comp_eq`). Every
   isomorphism-invariant Borel observable into a countably separated measurable space has the same
   fibres as a countable sentence list (`exists_sentenceTheory_eq_iff_of_countablySeparated`). In
   particular, if `f : (ι → Bool) → RelationalConfiguration L V` is measurable with pairwise
   non-isomorphic values on a countable index type `ι`, some `θ : ι → L.Sentenceω` recovers every
   bit via `sentenceTheory θ (f x) = x` (`exists_sentenceTheory_apply_eq`).
2. **Sentence-spectrum characterization of thinness.** On a countable carrier in a countable
   relational vocabulary, a Borel set `C` is thin for isomorphism if and only if every countable
   sequence `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on `C`
   (`isThinOn_iff_countable_image_sentenceTheory`, and
   `isThinOnNatModels_iff_countable_image_sentenceTheory` for model classes on `ℕ`). The reverse
   implication (`isThinOn_of_forall_countable_image_sentenceTheory`) requires neither measurability
   nor isomorphism invariance of `C`.
3. **Single-sentence splits.** If `classOf : C → Q` presents `C` so that truth of `L_{ω₁ω}`
   sentences factors through `classOf` and every single sentence has a truth side meeting only
   countably many points of `Q`, then every countable sentence list realizes countably many truth
   sequences on `C` and hence `C` is thin (`isThinOn_of_splits_along`, `isThinOn_of_holds_splits`,
   `isThinOn_of_sentence_splits`). Neither measurability nor isomorphism invariance of `C`, nor any
   topology, σ-algebra, or surjectivity on `Q`, is assumed. For `L_{ω₁ω}` model classes on `ℕ`,
   concentration at all countable back-and-forth levels is equivalent to every single-sentence cut
   having a side with countably many models up to isomorphism
   (`concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`).
4. **Smooth complete invariants.** On a Borel class `C`, restricted isomorphism is smooth
   (`Setoid.IsSmooth`) if and only if a single countable sequence `θ : ℕ → L.Sentenceω` separates
   non-isomorphic members of `C` (`isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`). Moreover,
   a Borel class meets countably many isomorphism classes if and only if it is both thin and smooth
   (`countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`).

## Main results

* `TauCeti.exists_sentenceTheory_comp_eq` and
  `TauCeti.exists_sentenceTheory_eq_iff_of_countablySeparated`: Borel observables into `ι → Bool`
  and into countably separated measurable spaces are realized by `L_{ω₁ω}` sentence lists.
* `TauCeti.exists_sentenceTheory_apply_eq` and `TauCeti.exists_forall_mem_modelsOf_iff`: Cantor
  recovery along measurable antichains from `ι → Bool`.
* `TauCeti.isThinOn_iff_countable_image_sentenceTheory` and
  `TauCeti.isThinOnNatModels_iff_countable_image_sentenceTheory`: thinness of Borel configuration
  sets and sentences via countable `L_{ω₁ω}` sentence spectra.
* `TauCeti.isThinOn_of_splits_along`, `TauCeti.isThinOn_of_holds_splits`, and
  `TauCeti.isThinOn_of_sentence_splits`: thinness from single-sentence countable splits, yielding
  `TauCeti.bfScattered_of_measurableSet_of_sentence_splits`,
  `TauCeti.concentratedAtBFLevels_of_measurableSet_of_sentence_splits`, and
  `TauCeti.concentratedAtBFLevels_modelsOf_iff_forall_countable_quotient_isoSetoidOn`.
* `TauCeti.isSmooth_comap_isoSetoid_iff_exists_sentenceTheory`,
  `TauCeti.countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth`,
  `TauCeti.countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth`, and
  `TauCeti.countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth`: smooth complete
  invariants and countable quotients on Borel classes and model classes.

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

/-! ### Borel observables and Cantor recovery -/

section Observables

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {ι : Type uι}

/-- **Borel observables into Boolean products.** Along a measurable family `f : X →
RelationalConfiguration L V` from a standard Borel space `X`, every isomorphism-invariant
measurable map `g : X → ι → Bool` is realized as `sentenceTheory θ ∘ f` for a family
`θ : ι → L.Sentenceω`. The index type `ι` need not be countable. -/
theorem exists_sentenceTheory_comp_eq {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → ι → Bool} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ι → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = g x := by
  have hcoord (i : ι) : ∃ φ : L.Sentenceω, ∀ x, f x ∈ modelsOf φ ↔ g x i = true := by
    have hgi : Measurable fun x => g x i := (measurable_pi_apply i).comp hg
    refine exists_sentence_mem_modelsOf_iff hf (hgi (measurableSet_singleton true))
      fun x y hxy => ?_
    simp only [mem_preimage, mem_singleton_iff, hinv x y hxy]
  choose θ hθ using hcoord
  refine ⟨θ, fun x => funext fun i => Bool.eq_iff_iff.2 ?_⟩
  simpa only [sentenceTheory_eq_true_iff] using hθ i x

/-- **Borel observables into countably separated spaces.** If `Z` is a countably separated
measurable space and `g : X → Z` is an isomorphism-invariant measurable map along a standard Borel
family `f : X → RelationalConfiguration L V`, there are a measurable injection `e : Z → ℕ → Bool`
and sentences `θ : ℕ → L.Sentenceω` such that `e (g x) = sentenceTheory θ (f x)` for all `x`. -/
theorem exists_measurable_injective_comp_eq_sentenceTheory
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → Z} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ (e : Z → ℕ → Bool) (θ : ℕ → L.Sentenceω),
      Measurable e ∧ Function.Injective e ∧ ∀ x, e (g x) = sentenceTheory θ (f x) := by
  obtain ⟨e, he_meas, he_inj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Z
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq hf (he_meas.comp hg)
    fun x y hxy => congrArg e (hinv x y hxy)
  exact ⟨e, θ, he_meas, he_inj, fun x => (hθ x).symm⟩

/-- **Fibrewise representation of Borel observables.** Any isomorphism-invariant measurable map
`g : X → Z` from a standard Borel family into a countably separated measurable space `Z` has the
same fibres as `sentenceTheory θ ∘ f` for some countable sequence `θ : ℕ → L.Sentenceω`. -/
theorem exists_sentenceTheory_eq_iff_of_countablySeparated
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → Z} (hg : Measurable g)
    (hinv : ∀ x y, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω,
      ∀ x y, g x = g y ↔ sentenceTheory θ (f x) = sentenceTheory θ (f y) := by
  obtain ⟨e, θ, -, he_inj, heq⟩ := exists_measurable_injective_comp_eq_sentenceTheory hf hg hinv
  exact ⟨θ, fun x y => ⟨fun h => by rw [← heq x, ← heq y, h],
    fun h => he_inj (by rw [heq x, heq y, h])⟩⟩

/-- **Cantor recovery.** For a countable index type `ι` (in particular `ι = ℕ`) and a measurable
map `f : (ι → Bool) → RelationalConfiguration L V` sending distinct points to non-isomorphic
configurations, some `θ : ι → L.Sentenceω` satisfies `sentenceTheory θ (f x) = x` for every `x`. -/
theorem exists_sentenceTheory_apply_eq [Countable ι]
    {f : (ι → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hne : ∀ x y, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ι → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = x :=
  exists_sentenceTheory_comp_eq hf measurable_id fun x y hxy =>
    by_contra fun h => hne x y h hxy

/-- Coordinatewise form of Cantor recovery: some `θ : ι → L.Sentenceω` satisfies
`f x ∈ modelsOf (θ i) ↔ x i = true` for every `x : ι → Bool` and `i : ι`. -/
theorem exists_forall_mem_modelsOf_iff [Countable ι]
    {f : (ι → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hne : ∀ x y, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ι → L.Sentenceω, ∀ x i, f x ∈ modelsOf (θ i) ↔ x i = true := by
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_apply_eq hf hne
  refine ⟨θ, fun x i => ?_⟩
  simpa only [sentenceTheory_eq_true_iff] using
    (congrArg (· = true) (congrFun (hθ x) i)).to_iff

end Observables

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
  have hcount : Countable (ℕ → Bool) := countable_univ_iff.1 huniv
  have hcard : #(ℕ → Bool) = 𝔠 := by
    rw [mk_arrow, mk_bool, mk_nat, lift_id, lift_id, two_power_aleph0]
  exact (hcard.symm ▸ aleph0_lt_continuum).not_ge (mk_le_aleph0_iff.2 hcount)

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
  let g : C → ι → Bool := fun c => sentenceTheory θ c.1
  have hg : Measurable g := (measurable_sentenceTheory θ).comp measurable_subtype_coe
  let F : Setoid C := (⊥ : Setoid (ι → Bool)).comap g
  have hF_meas : MeasurableSet {p : C × C | F p.1 p.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd)
  have hcount : Countable (Quotient F) :=
    (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V) F
      (fun x y hxy => sentenceTheory_eq_of_isoSetoid hxy θ) hF_meas).resolve_right
      (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin)
  let qMap : Quotient F → ι → Bool := Quotient.lift g fun _ _ h => h
  have hsub : sentenceTheory θ '' C ⊆ range qMap := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨Quotient.mk F ⟨c, hc⟩, rfl⟩
  exact (countable_range qMap).mono hsub

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
      c.1 ∈ modelsOf φ ↔ d.1 ∈ modelsOf φ)
    (hsplit : ∀ φ : L.Sentenceω,
      (classOf '' {c : C | c.1 ∈ modelsOf φ}).Countable ∨
        (classOf '' {c : C | c.1 ∉ modelsOf φ}).Countable)
    (θ : ι → L.Sentenceω) :
    (sentenceTheory θ '' C).Countable := by
  let R := range classOf
  let rep : R → C := fun q => q.2.choose
  have hrep (q : R) : classOf (rep q) = q.1 := q.2.choose_spec
  let P : ι → R → Prop := fun i q => (rep q).1 ∈ modelsOf (θ i)
  have hP_split (i : ι) : {q : R | P i q}.Countable ∨ {q : R | ¬ P i q}.Countable := by
    rcases hsplit (θ i) with hpos | hneg
    · refine .inl ((hpos.preimage Subtype.val_injective).mono fun q hq => ?_)
      exact ⟨rep q, hq, hrep q⟩
    · refine .inr ((hneg.preimage Subtype.val_injective).mono fun q hq => ?_)
      exact ⟨rep q, hq, hrep q⟩
  let g : R → ι → Bool := fun q => sentenceTheory θ (rep q).1
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
      c.1 ∈ modelsOf φ ↔ d.1 ∈ modelsOf φ)
    (hsplit : ∀ φ : L.Sentenceω,
      (classOf '' {c : C | c.1 ∈ modelsOf φ}).Countable ∨
        (classOf '' {c : C | c.1 ∉ modelsOf φ}).Countable) :
    (isoSetoid L V).IsThinOn C :=
  isThinOn_of_forall_countable_image_sentenceTheory
    (countable_image_sentenceTheory_of_splits_along classOf htruth hsplit)

/-- Presentation form with an explicit truth predicate `holds : L.Sentenceω → Q → Prop`: if truth
on `C` is read through `holds` along `classOf : C → Q` and each sentence holds or fails on only
countably many points of `Q`, then `C` is thin for isomorphism. -/
theorem isThinOn_of_holds_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} {Q : Type*}
    (classOf : C → Q) (holds : L.Sentenceω → Q → Prop)
    (hholds : ∀ (φ : L.Sentenceω) (c : C), c.1 ∈ modelsOf φ ↔ holds φ (classOf c))
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
  let classOf : C → Quotient (isoSetoid L V) := fun c => Quotient.mk (isoSetoid L V) c.1
  refine isThinOn_of_splits_along classOf
    (fun c d hcd φ => (isomorphismInvariant_modelsOf φ).mem_iff (Quotient.exact hcd)) fun θ => ?_
  have hpos : classOf '' {c : C | c.1 ∈ modelsOf θ} =
      Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ) := by
    ext q
    simp only [classOf, mem_image, Subtype.exists, mem_ofPred_eq, mem_inter_iff]
    exact ⟨fun ⟨c, hc, hθ, hq⟩ => ⟨c, ⟨hc, hθ⟩, hq⟩,
      fun ⟨c, ⟨hc, hθ⟩, hq⟩ => ⟨c, hc, hθ, hq⟩⟩
  have hneg : classOf '' {c : C | c.1 ∉ modelsOf θ} =
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

end Splits

/-! ### Smooth complete invariants on Borel classes -/

section Smooth

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V] {κ : Type uκ}

omit [∀ n, Countable (L.Relations n)] in
/-- If a countable sequence of sentences with countable branching separates non-isomorphic members
of `C`, then restricted isomorphism on `C` is smooth. No measurability of `C` or countability of `L`
is required. -/
theorem isSmooth_comap_isoSetoid_of_exists_sentenceTheory [Countable κ]
    {C : Set (RelationalConfiguration L V)}
    (h : ∃ θ : ℕ → L.SentenceInf κ, ∀ c ∈ C, ∀ d ∈ C,
      isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth := by
  obtain ⟨θ, hθ⟩ := h
  exact Setoid.isSmooth_iff.2 ⟨fun c : C => sentenceTheory θ c.1,
    (measurable_sentenceTheory θ).comp measurable_subtype_coe,
    fun x y => hθ x.1 x.2 y.1 y.2⟩

/-- **Smoothness via complete countable sentence lists.** On a Borel subset `C` of configurations
over a countable carrier in a countable relational vocabulary, restricted isomorphism is smooth if
and only if a single countable sequence `θ : ℕ → L.Sentenceω` decides isomorphism within `C`. -/
theorem isSmooth_comap_isoSetoid_iff_exists_sentenceTheory
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω, ∀ c ∈ C, ∀ d ∈ C,
        isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d := by
  refine ⟨fun hsmooth => ?_, isSmooth_comap_isoSetoid_of_exists_sentenceTheory⟩
  have : StandardBorelSpace C := hC.standardBorel
  obtain ⟨g, hg, hgE⟩ := Setoid.isSmooth_iff.1 hsmooth
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq (f := (Subtype.val : C → _))
    measurable_subtype_coe hg fun x y hxy => (hgE x y).1 hxy
  exact ⟨θ, fun c hc d hd => (hgE ⟨c, hc⟩ ⟨d, hd⟩).trans
    ⟨fun h => by rw [hθ ⟨c, hc⟩, hθ ⟨d, hd⟩, h],
      fun h => by rwa [hθ ⟨c, hc⟩, hθ ⟨d, hd⟩] at h⟩⟩

/-- **Thin smooth Borel classes have countably many isomorphism classes.** If `C` is Borel, thin
for isomorphism, and carries a Borel complete invariant (`IsSmooth`), then `C` meets only countably
many isomorphism classes. -/
theorem countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C)
    (hsmooth : ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
    ((isoSetoid L V).comap (Subtype.val : C → _)) (fun _ _ h => h)
    hsmooth.measurableSet_setOf).resolve_right
    (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin)

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
    have horbit : {d : RelationalConfiguration L V | isoSetoid L V x.1 d} =
        modelsOf (@scottSentence L _ V x.1.toStructure _ _) := by
      ext d
      exact isoSetoid_apply.trans
        ((@realize_scottSentence_iff L _ _ V x.1.toStructure _ V d.toStructure _).symm.trans
          mem_modelsOf.symm)
    exact (horbit ▸ measurableSet_modelsOf _).preimage measurable_subtype_coe

/-- An infinitary sentence `φ` with countable branching has countably many models on `ℕ` up to
isomorphism if and only if `φ` is thin on `ℕ` and `isoSetoidOn ℕ φ` is smooth. -/
theorem countable_quotient_isoSetoidOn_nat_iff_isThinOnNatModels_and_isSmooth [Countable κ]
    {φ : L.SentenceInf κ} :
    Countable (Quotient (isoSetoidOn ℕ φ)) ↔
      IsThinOnNatModels φ ∧ (isoSetoidOn ℕ φ).IsSmooth := by
  rw [isoSetoidOn, countable_quotient_comap_isoSetoid_iff_isThinOn_and_isSmooth
    (measurableSet_modelsOf φ), isThinOnNatModels_iff_isThinOn]

end Smooth

end TauCeti
