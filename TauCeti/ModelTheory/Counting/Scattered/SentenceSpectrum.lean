/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.Data.Set.Countable
import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Sentence spectra, single-sentence splits, and Borel observables on thin classes

Given an indexed family of infinitary sentences `θ : I → L.SentenceInf ι` and a relational
configuration `c` on a carrier `V`, the **sentence theory** `sentenceTheory θ c : I → Bool`
records which sentences `θ i` hold in `c.toStructure`. When each `θ i` has countable branching and
`V` is countable, `sentenceTheory θ` is Borel measurable and constant on isomorphism classes.

Combining relative López–Escobar separation (`exists_sentence_mem_modelsOf_iff`) with relative
Silver dichotomy (`Setoid.countable_or_hasCantorAntichainOn_of_measurableSet`) yields three groups
of results in a relational vocabulary with countably many relation symbols of each arity on a
countable carrier `V`:

1. **Sentence-spectrum characterization of thinness** (`isThinOn_iff_countable_sentenceSpectra`,
   `isThinOnNatModels_iff_countable_sentenceSpectra`). A Borel set `C` of configurations carries no
   perfect set of pairwise non-isomorphic configurations if and only if every sequence of `L_{ω₁ω}`
   sentences `θ : ℕ → L.Sentenceω` realizes only countably many truth sequences on `C`. No
   isomorphism invariance of `C` is assumed, and the converse implication
   (`isThinOn_of_countable_sentenceSpectra`) needs no measurability hypothesis on `C`.
2. **Thinness from single-sentence splits** (`isThinOn_of_sentence_splits_along`,
   `isThinOn_of_countable_isoClasses_inter_or_sdiff`). If a presentation `classOf : C → Q` through
   which truth of every `L_{ω₁ω}` sentence factors has a countable truth side in `Q` for every
   sentence, then every countable family of sentences realizes only countably many truth sequences
   on `C` (`countable_sentenceTheory_image_of_splits_along`), so `C` is thin — with no
   measurability, invariance, surjectivity, or σ-algebra hypothesis on `C` or `Q`. On `ℕ`, a Borel
   set whose every sentence cut has a countable isomorphism-class side is therefore thin, scattered,
   and concentrated at back-and-forth levels
   (`concentratedAtBFLevels_of_measurableSet_of_sentence_splits`).
3. **Borel observables and smooth complete invariants**
   (`exists_sentenceTheory_comp_eq_of_measurable`,
   `exists_sentenceTheory_eq_iff_of_countablySeparated`,
   `isSmooth_comap_isoSetoid_iff_exists_complete_sentences`,
   `countable_quotient_comap_isoSetoid_iff_isSmooth`). Every isomorphism-invariant Borel observable
   from a standard Borel parameter space `X` into Cantor space `ℕ → Bool` is the sentence theory of
   a countable sequence of `L_{ω₁ω}` sentences, and every invariant Borel map into a countably
   separated measurable space has the same fibres as such a sentence theory. Consequently,
   isomorphism restricted to a Borel set `C` is smooth (`Setoid.IsSmooth`) iff a countable list of
   `L_{ω₁ω}` sentences forms a complete invariant on `C`; and when `C` is Borel and thin, smoothness
   of isomorphism on `C` is equivalent to `C` meeting only countably many isomorphism classes.

## Main definitions

* `TauCeti.RelationalConfiguration.sentenceTheory`: the Boolean truth assignment
  `i ↦ decide (c ∈ modelsOf (θ i))` of a family of infinitary sentences `θ : I → L.SentenceInf ι`
  at a configuration `c`.

## Main results

* `TauCeti.RelationalConfiguration.measurable_sentenceTheory` and
  `FirstOrder.Language.Equiv.sentenceTheory_eq`: measurability and cross-carrier isomorphism
  invariance of `sentenceTheory`.
* `TauCeti.RelationalConfiguration.exists_sentenceTheory_comp_eq`: Cantor recovery in
  `sentenceTheory` form.
* `TauCeti.RelationalConfiguration.isThinOn_iff_countable_sentenceSpectra` and
  `TauCeti.isThinOnNatModels_iff_countable_sentenceSpectra`: a Borel class (or sentence on `ℕ`) is
  thin iff every countable sequence of `L_{ω₁ω}` sentences has countable spectrum on it.
* `TauCeti.RelationalConfiguration.isThinOn_of_sentence_splits_along` and
  `TauCeti.RelationalConfiguration.isThinOn_of_countable_isoClasses_inter_or_sdiff`: single-sentence
  splits force thinness without Borelness or invariance hypotheses.
* `TauCeti.concentratedAtBFLevels_of_measurableSet_of_sentence_splits`: a Borel set on `ℕ` whose
  sentence cuts each have a countable isomorphism-class side is concentrated at back-and-forth
  levels.
* `TauCeti.RelationalConfiguration.exists_sentenceTheory_comp_eq_of_measurable` and
  `TauCeti.RelationalConfiguration.exists_sentenceTheory_eq_iff_of_countablySeparated`: invariant
  Borel observables are realized by countable lists of `L_{ω₁ω}` sentences.
* `TauCeti.RelationalConfiguration.isSmooth_comap_isoSetoid_iff_exists_complete_sentences`,
  `TauCeti.RelationalConfiguration.countable_quotient_comap_isoSetoid_iff_isSmooth`, and
  `TauCeti.IsThinOnNatModels.countable_quotient_isoSetoidOn_iff_isSmooth`: smooth complete
  invariants vs. countable sentence lists and countability of isomorphism classes on thin Borel
  sets.

## References

* E. G. K. Lopez-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae 57 (1965), 253–272.
* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* Su Gao, *Invariant Descriptive Set Theory*, Monographs and Surveys in Pure and Applied
  Mathematics 150, CRC Press, 2009, Chapters 5 and 11.
* Adapted in part from `sentenceTheory` and `isThin_iff_countable_sentenceSpectra` in
  `InfinitaryLogic/Descriptive/SentenceRecovery.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` at checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`
  (Apache-2.0), generalized here to arbitrary countable carriers, general index and branching types,
  presentation-relative single-sentence splits, and smooth Borel observables.
-/

public section

universe u v w w' uι uI uQ uX uY

open Cardinal FirstOrder FirstOrder.Language MeasureTheory MeasurableSpace Set

namespace TauCeti.RelationalConfiguration

/-! ### Sentence theories and invariance -/

section SentenceTheory

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι} {I : Type uI}
variable {V : Type w} {W : Type w'}

/-- The **sentence theory** of a configuration `c` with respect to an indexed family of infinitary
sentences `θ : I → L.SentenceInf ι`: the `I`-indexed Boolean sequence recording which `θ i` hold in
`c.toStructure`. -/
noncomputable def sentenceTheory (θ : I → L.SentenceInf ι) (c : RelationalConfiguration L V) :
    I → Bool :=
  open Classical in fun i => decide (c ∈ modelsOf (θ i))

theorem sentenceTheory_apply (θ : I → L.SentenceInf ι) (c : RelationalConfiguration L V) (i : I) :
    sentenceTheory θ c i =
      @decide (c ∈ modelsOf (θ i)) (Classical.propDecidable _) :=
  (rfl)

@[simp]
theorem sentenceTheory_apply_eq_true_iff (θ : I → L.SentenceInf ι)
    (c : RelationalConfiguration L V) (i : I) :
    sentenceTheory θ c i = true ↔ c ∈ modelsOf (θ i) := by
  classical
  simp [sentenceTheory]

@[simp]
theorem sentenceTheory_apply_eq_false_iff (θ : I → L.SentenceInf ι)
    (c : RelationalConfiguration L V) (i : I) :
    sentenceTheory θ c i = false ↔ c ∉ modelsOf (θ i) := by
  classical
  simp [sentenceTheory]

/-- Two configurations have the same `sentenceTheory θ` exactly when they satisfy the same
sentences `θ i` for all `i : I`. -/
theorem sentenceTheory_eq_iff (θ : I → L.SentenceInf ι)
    {c : RelationalConfiguration L V} {d : RelationalConfiguration L W} :
    sentenceTheory θ c = sentenceTheory θ d ↔
      ∀ i, c ∈ modelsOf (θ i) ↔ d ∈ modelsOf (θ i) := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [Bool.eq_iff_iff, sentenceTheory_apply_eq_true_iff, sentenceTheory_apply_eq_true_iff]

/-- In a relational language, `sentenceTheory θ` is Borel measurable whenever `V` and the branching
index `ι` are countable. No countability assumption on `L` or on the list index `I` is needed. -/
@[fun_prop]
theorem measurable_sentenceTheory [Countable ι] [Countable V] (θ : I → L.SentenceInf ι) :
    Measurable (sentenceTheory (V := V) θ) := by
  classical
  refine measurable_pi_iff.mpr fun i => ?_
  have heq : (fun c : RelationalConfiguration L V => sentenceTheory θ c i) =
      fun c => if c ∈ modelsOf (θ i) then true else false := by
    funext c
    by_cases h : c ∈ modelsOf (θ i) <;> simp [sentenceTheory, h]
  rw [heq]
  exact Measurable.ite (measurableSet_modelsOf (θ i)) measurable_const measurable_const

/-- Isomorphic configurations on possibly different carriers have the same `sentenceTheory`. -/
theorem _root_.FirstOrder.Language.Equiv.sentenceTheory_eq {c : RelationalConfiguration L V}
    {d : RelationalConfiguration L W} (e : @Language.Equiv L V W c.toStructure d.toStructure)
    (θ : I → L.SentenceInf ι) :
    sentenceTheory θ c = sentenceTheory θ d :=
  (sentenceTheory_eq_iff θ).mpr fun i => e.mem_modelsOf_iff (θ i)

/-- Isomorphic configurations on the same carrier have the same `sentenceTheory`. -/
theorem sentenceTheory_eq_of_isoSetoid (θ : I → L.SentenceInf ι)
    {c d : RelationalConfiguration L V} (h : isoSetoid L V c d) :
    sentenceTheory θ c = sentenceTheory θ d := by
  obtain ⟨e⟩ := isoSetoid_apply.mp h
  exact e.sentenceTheory_eq θ

end SentenceTheory

/-! ### Sentence spectra and thinness -/

section SentenceSpectra

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- **Combinatorial single-sentence split bound.** If truth of every sentence `θ i` in a countable
family factors through a presentation `classOf : C → Q` and each `θ i` has a countable truth side
in `Q`, then `θ` realizes only countably many truth sequences on `C`. No measurability, invariance,
surjectivity, or countability hypothesis on `L`, `V`, `C`, or `Q` is required. -/
theorem countable_sentenceTheory_image_of_splits_along {ι : Type uι} {I : Type uI} [Countable I]
    {C : Set (RelationalConfiguration L V)} {Q : Type uQ} (classOf : C → Q)
    (θ : I → L.SentenceInf ι)
    (hdet : ∀ ⦃c d : C⦄, classOf c = classOf d →
      ∀ i, (c : RelationalConfiguration L V) ∈ modelsOf (θ i) ↔
        (d : RelationalConfiguration L V) ∈ modelsOf (θ i))
    (hsplit : ∀ i,
      (classOf '' {c : C | (c : RelationalConfiguration L V) ∈ modelsOf (θ i)}).Countable ∨
        (classOf '' {c : C | (c : RelationalConfiguration L V) ∉ modelsOf (θ i)}).Countable) :
    (sentenceTheory θ '' C).Countable := by
  let rep : range classOf → C := fun q => q.2.choose
  have hrep (q : range classOf) : classOf (rep q) = q.1 := q.2.choose_spec
  let P : I → range classOf → Prop := fun i q =>
    (rep q : RelationalConfiguration L V) ∈ modelsOf (θ i)
  let g : range classOf → I → Bool := fun q => sentenceTheory θ (rep q).1
  have hg : ∀ x y, (∀ i, P i x ↔ P i y) → g x = g y := fun x y h =>
    (sentenceTheory_eq_iff θ).mpr h
  have hPsplit (i : I) : {q | P i q}.Countable ∨ {q | ¬ P i q}.Countable := by
    have hmap₁ : MapsTo Subtype.val {q | P i q}
        (classOf '' {c : C | (c : RelationalConfiguration L V) ∈ modelsOf (θ i)}) :=
      fun q hq => ⟨rep q, hq, hrep q⟩
    have hmap₂ : MapsTo Subtype.val {q | ¬ P i q}
        (classOf '' {c : C | (c : RelationalConfiguration L V) ∉ modelsOf (θ i)}) :=
      fun q hq => ⟨rep q, hq, hrep q⟩
    exact (hsplit i).imp (hmap₁.countable_of_injOn Subtype.val_injective.injOn)
      (hmap₂.countable_of_injOn Subtype.val_injective.injOn)
  refine (countable_range_of_splits g hg hPsplit).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  let q : range classOf := ⟨classOf ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩
  exact ⟨q, (sentenceTheory_eq_iff θ).mpr fun i => hdet (c := rep q) (d := ⟨c, hc⟩) (hrep q) i⟩

variable [∀ n, Countable (L.Relations n)] [Countable V]

/-- **Cantor recovery via `sentenceTheory`.** For a Borel map `f : (ℕ → Bool) →
RelationalConfiguration L V` sending distinct sequences to non-isomorphic configurations, there is a
sequence of `L_{ω₁ω}` sentences `θ : ℕ → L.Sentenceω` with `sentenceTheory θ (f x) = x` for every
`x : ℕ → Bool`. -/
theorem exists_sentenceTheory_comp_eq {f : (ℕ → Bool) → RelationalConfiguration L V}
    (hf : Measurable f) (hnoniso : ∀ ⦃x y⦄, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = x := by
  obtain ⟨θ, hθ⟩ := exists_sentences_mem_modelsOf_iff hf hnoniso
  refine ⟨θ, fun x => funext fun n => ?_⟩
  rw [Bool.eq_iff_iff, sentenceTheory_apply_eq_true_iff]
  exact hθ x n

/-- **Countable sentence spectra rule out Cantor antichains.** If every countable sequence of
`L_{ω₁ω}` sentences realizes only countably many truth sequences on `C`, then `C` carries no Cantor
antichain for isomorphism. No measurability or invariance of `C` is required. -/
theorem not_hasCantorAntichainOn_of_countable_sentenceSpectra
    {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    ¬ (isoSetoid L V).HasCantorAntichainOn C := by
  intro hcantor
  obtain ⟨f, hf, hrange, hnoniso⟩ := Setoid.hasCantorAntichainOn_iff.mp hcantor
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq hf.measurable fun x y hne => hnoniso x y hne
  have huniv : (univ : Set (ℕ → Bool)).Countable := by
    refine (hspec θ).mono ?_
    rintro x -
    exact ⟨f x, hrange x, hθ x⟩
  have hcard : #(ℕ → Bool) ≤ ℵ₀ := mk_le_aleph0_iff.mpr (countable_univ_iff.mp huniv)
  exact (by simpa using aleph0_lt_continuum : ℵ₀ < #(ℕ → Bool)).not_ge hcard

/-- **Countable sentence spectra imply thinness.** If every sequence `θ : ℕ → L.Sentenceω` has
countable spectrum on `C`, then `C` is thin for isomorphism, without assuming `C` is Borel. -/
theorem isThinOn_of_countable_sentenceSpectra {C : Set (RelationalConfiguration L V)}
    (hspec : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    (isoSetoid L V).IsThinOn C :=
  Setoid.isThinOn_iff_not_hasCantorAntichainOn.mpr
    (not_hasCantorAntichainOn_of_countable_sentenceSpectra hspec)

/-- **Thin Borel sets have countable sentence spectra.** On a Borel set `C` of configurations that
is thin for isomorphism, every countable family of infinitary sentences `θ : I → L.SentenceInf ι`
with countable branching realizes only countably many truth assignments on `C`. -/
theorem _root_.Setoid.IsThinOn.countable_sentenceTheory_image {ι : Type uι} [Countable ι]
    {I : Type uI} [Countable I] {C : Set (RelationalConfiguration L V)}
    (hthin : (isoSetoid L V).IsThinOn C) (hC : MeasurableSet C) (θ : I → L.SentenceInf ι) :
    (sentenceTheory θ '' C).Countable := by
  let g : C → I → Bool := fun x => sentenceTheory θ x.1
  have hg : Measurable g := (measurable_sentenceTheory θ).comp measurable_subtype_coe
  let F : Setoid C := (⊥ : Setoid (I → Bool)).comap g
  have hRF : ∀ x y : C, isoSetoid L V x y → F x y := fun x y hxy =>
    sentenceTheory_eq_of_isoSetoid θ hxy
  have hF : MeasurableSet {p : C × C | F p.1 p.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) (hg.comp measurable_snd)
  have : Countable (Quotient F) :=
    (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V) F hRF hF)
      |>.resolve_right (Setoid.isThinOn_iff_not_hasCantorAntichainOn.mp hthin)
  let liftG : Quotient F → I → Bool := Quotient.lift g fun _ _ h => h
  refine (countable_range liftG).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨Quotient.mk F ⟨c, hc⟩, rfl⟩

/-- **Sentence-spectrum characterization of thinness.** On a countable carrier in a relational
language with countably many relation symbols of each arity, a Borel set `C` of configurations is
thin for isomorphism if and only if every sequence of `L_{ω₁ω}` sentences `θ : ℕ → L.Sentenceω`
realizes only countably many truth sequences on `C`. No isomorphism invariance of `C` is assumed. -/
theorem isThinOn_iff_countable_sentenceSpectra {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) :
    (isoSetoid L V).IsThinOn C ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable :=
  ⟨fun h θ => h.countable_sentenceTheory_image hC θ, isThinOn_of_countable_sentenceSpectra⟩

/-- **Single-sentence splits force thinness along any presentation.** Let `classOf : C → Q` be a
presentation of `C` through which satisfaction of every `L_{ω₁ω}` sentence factors, and suppose
every sentence has a truth side meeting only countably many points of `Q`. Then `C` is thin for
isomorphism. No measurability or invariance of `C`, and no surjectivity or σ-algebra on `Q`, is
assumed. -/
theorem isThinOn_of_sentence_splits_along {C : Set (RelationalConfiguration L V)} {Q : Type uQ}
    (classOf : C → Q)
    (hdet : ∀ ⦃c d : C⦄, classOf c = classOf d →
      ∀ θ : L.Sentenceω, (c : RelationalConfiguration L V) ∈ modelsOf θ ↔
        (d : RelationalConfiguration L V) ∈ modelsOf θ)
    (hsplit : ∀ θ : L.Sentenceω,
      (classOf '' {c : C | (c : RelationalConfiguration L V) ∈ modelsOf θ}).Countable ∨
        (classOf '' {c : C | (c : RelationalConfiguration L V) ∉ modelsOf θ}).Countable) :
    (isoSetoid L V).IsThinOn C :=
  isThinOn_of_countable_sentenceSpectra fun θ =>
    countable_sentenceTheory_image_of_splits_along classOf θ
      (fun _ _ h n => hdet h (θ n)) fun n => hsplit (θ n)

/-- **Single-sentence splits in `Quotient (isoSetoid L V)` force thinness.** If every `L_{ω₁ω}`
sentence cut of `C` has a side meeting only countably many isomorphism classes, then `C` is thin for
isomorphism, without assuming `C` is Borel or isomorphism invariant. -/
theorem isThinOn_of_countable_isoClasses_inter_or_sdiff {C : Set (RelationalConfiguration L V)}
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ)).Countable) :
    (isoSetoid L V).IsThinOn C := by
  refine isThinOn_of_sentence_splits_along (fun c : C => Quotient.mk (isoSetoid L V) c.1)
    (fun c d hcd θ => ?_) fun θ => ?_
  · obtain ⟨e⟩ := isoSetoid_apply.mp (Quotient.exact hcd)
    exact e.mem_modelsOf_iff θ
  · refine (hsplit θ).imp (fun hc => hc.mono ?_) (fun hc => hc.mono ?_)
    · rintro _ ⟨⟨c, hcC⟩, hcθ, rfl⟩
      exact ⟨c, ⟨hcC, hcθ⟩, rfl⟩
    · rintro _ ⟨⟨c, hcC⟩, hcθ, rfl⟩
      exact ⟨c, ⟨hcC, hcθ⟩, rfl⟩

end SentenceSpectra

/-! ### Borel observables and smooth complete invariants -/

section BorelObservables

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {V : Type w} [Countable V]

/-- On a countable carrier, every single isomorphism class of configurations is Borel: it is the
model class of the canonical Scott sentence of `c.toStructure`. -/
theorem measurableSet_isoSetoid_class (c : RelationalConfiguration L V) :
    MeasurableSet {d : RelationalConfiguration L V | isoSetoid L V c d} := by
  have : Countable (Σ k, L.Relations k) := inferInstance
  have hmod : modelsOf (V := V) (@scottSentence L _ V c.toStructure _ _) =
      {d | isoSetoid L V c d} := by
    ext d
    exact (mem_modelsOf.trans
      (@realize_scottSentence_iff L _ _ V c.toStructure _ V d.toStructure _)).trans
      isoSetoid_apply.symm
  rw [← hmod]
  exact measurableSet_modelsOf _

/-- **Borel observables into Cantor space.** Let `X` be a standard Borel space and
`f : X → RelationalConfiguration L V` a Borel family of configurations. Every Borel observable
`g : X → ℕ → Bool` invariant under isomorphism of the configurations `f x` is realized as
`x ↦ sentenceTheory θ (f x)` for some sequence of sentences `θ : ℕ → L.Sentenceω`. -/
theorem exists_sentenceTheory_comp_eq_of_measurable {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → ℕ → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = g x := by
  have hcoord (n : ℕ) : ∃ ψ : L.Sentenceω, ∀ x, f x ∈ modelsOf ψ ↔ g x n = true :=
    exists_sentence_mem_modelsOf_iff (U := {x | g x n = true}) hf
      (((measurable_pi_apply n).comp hg) (measurableSet_singleton true))
      fun x y hxy hx => by simpa only [mem_ofPred_eq, ← congrFun (hinv hxy) n] using hx
  choose θ hθ using hcoord
  refine ⟨θ, fun x => funext fun n => ?_⟩
  rw [Bool.eq_iff_iff, sentenceTheory_apply_eq_true_iff]
  exact hθ n x

/-- **Borel observables into countably separated spaces.** Let `X` be a standard Borel space, `Y` a
countably separated measurable space, `f : X → RelationalConfiguration L V` a Borel family, and
`g : X → Y` a Borel map invariant under isomorphism of `f x`. Then some sequence of sentences
`θ : ℕ → L.Sentenceω` has the same fibres on `X` as `g`. -/
theorem exists_sentenceTheory_eq_iff_of_countablySeparated {X : Type uX} [MeasurableSpace X]
    [StandardBorelSpace X] {Y : Type uY} [MeasurableSpace Y] [CountablySeparated Y]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) {g : X → Y} (hg : Measurable g)
    (hinv : ∀ ⦃x y⦄, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x y, g x = g y ↔ sentenceTheory θ (f x) = sentenceTheory θ (f y) := by
  obtain ⟨e, he, hinj⟩ := measurable_injection_nat_bool_of_countablySeparated Y
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq_of_measurable hf (he.comp hg)
    fun x y hxy => congrArg e (hinv hxy)
  refine ⟨θ, fun x y => ?_⟩
  rw [hθ x, hθ y]
  exact ⟨congrArg e, fun h => hinj h⟩

/-- **Smooth complete invariants vs. complete countable sentence lists.** On a Borel subset `C` of
configurations, isomorphism restricted to `C` is smooth (`Setoid.IsSmooth`) if and only if some
countable sequence `θ : ℕ → L.Sentenceω` is a complete isomorphism invariant on `C`. -/
theorem isSmooth_comap_isoSetoid_iff_exists_complete_sentences
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω, ∀ c ∈ C, ∀ d ∈ C,
        isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d := by
  have : StandardBorelSpace C := hC.standardBorel
  rw [Setoid.isSmooth_iff]
  constructor
  · rintro ⟨g, hg, hgE⟩
    obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq_of_measurable measurable_subtype_coe hg
      fun x y hxy => (hgE x y).mp hxy
    refine ⟨θ, fun c hc d hd => ?_⟩
    have hc' : sentenceTheory θ c = g ⟨c, hc⟩ := hθ ⟨c, hc⟩
    have hd' : sentenceTheory θ d = g ⟨d, hd⟩ := hθ ⟨d, hd⟩
    rw [hc', hd']
    exact hgE ⟨c, hc⟩ ⟨d, hd⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨fun x : C => sentenceTheory θ x.1,
      (measurable_sentenceTheory θ).comp measurable_subtype_coe,
      fun x y => hθ x.1 x.2 y.1 y.2⟩

/-- If a set `C` of configurations meets only countably many isomorphism classes, then isomorphism
restricted to `C` is smooth, even without assuming `C` is Borel. -/
theorem isSmooth_comap_isoSetoid_of_countable {C : Set (RelationalConfiguration L V)}
    [Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _)))] :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth :=
  Setoid.isSmooth_of_countable_quotient fun x =>
    (measurableSet_isoSetoid_class x.1).preimage measurable_subtype_coe

/-- **A thin Borel class with smooth isomorphism meets only countably many isomorphism classes.** -/
theorem countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C)
    (hsmooth : ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
    ((isoSetoid L V).comap Subtype.val) (fun _ _ h => h) hsmooth.measurableSet_setOf).resolve_right
    (Setoid.isThinOn_iff_not_hasCantorAntichainOn.mp hthin)

/-- On a thin Borel set `C` of configurations, `C` meets countably many isomorphism classes if and
only if isomorphism restricted to `C` is smooth. -/
theorem countable_quotient_comap_isoSetoid_iff_isSmooth {C : Set (RelationalConfiguration L V)}
    (hC : MeasurableSet C) (hthin : (isoSetoid L V).IsThinOn C) :
    Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) ↔
      ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth :=
  ⟨fun _ => isSmooth_comap_isoSetoid_of_countable,
    countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth hC hthin⟩

end BorelObservables

end TauCeti.RelationalConfiguration

namespace TauCeti

open RelationalConfiguration

/-! ### Sentence-level consequences on `ℕ` -/

section NatSentences

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]
variable {ι : Type uι} [Countable ι]

/-- **Sentence-spectrum characterization for `IsThinOnNatModels`.** An infinitary sentence `φ` with
countable branching is thin on its models on `ℕ` if and only if every sequence of `L_{ω₁ω}`
sentences realizes only countably many truth sequences on `modelsOf (V := ℕ) φ`. -/
theorem isThinOnNatModels_iff_countable_sentenceSpectra (φ : L.SentenceInf ι) :
    IsThinOnNatModels φ ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable := by
  rw [isThinOnNatModels_iff_isThinOn]
  exact isThinOn_iff_countable_sentenceSpectra (measurableSet_modelsOf φ)

/-- A sentence `φ` with countable branching that is thin on `ℕ` has countably many models on `ℕ` up
to isomorphism whenever `isoSetoidOn ℕ φ` is smooth. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_of_isSmooth {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) (hsmooth : (isoSetoidOn ℕ φ).IsSmooth) :
    Countable (Quotient (isoSetoidOn ℕ φ)) :=
  countable_quotient_comap_isoSetoid_of_isThinOn_of_isSmooth (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.mp h) hsmooth

/-- For a sentence `φ` with countable branching that is thin on `ℕ`, countability of the models of
`φ` on `ℕ` up to isomorphism is equivalent to smoothness of `isoSetoidOn ℕ φ`. -/
theorem IsThinOnNatModels.countable_quotient_isoSetoidOn_iff_isSmooth {φ : L.SentenceInf ι}
    (h : IsThinOnNatModels φ) :
    Countable (Quotient (isoSetoidOn ℕ φ)) ↔ (isoSetoidOn ℕ φ).IsSmooth :=
  countable_quotient_comap_isoSetoid_iff_isSmooth (measurableSet_modelsOf φ)
    (isThinOnNatModels_iff_isThinOn.mp h)

/-- A Borel set of configurations on `ℕ` whose every `L_{ω₁ω}` sentence cut has a side meeting only
countably many isomorphism classes is thin, hence back-and-forth scattered, hence concentrated at
every countable back-and-forth level. -/
theorem concentratedAtBFLevels_of_measurableSet_of_sentence_splits
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K)
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable) :
    ConcentratedAtBFLevels K := by
  have : Countable (Σ n, L.Relations n) := inferInstance
  exact concentratedAtBFLevels_of_bfScattered_of_sentence_splits
    (BFScattered.of_isThinOn hK (isThinOn_of_countable_isoClasses_inter_or_sdiff hsplit)) hsplit

end NatSentences

end TauCeti
