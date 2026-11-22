/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Spectrum
public import TauCeti.ModelTheory.Counting.Scattered.Vaught
import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
import TauCeti.ModelTheory.RelationalConfiguration.Saturation

/-!
# Minimally uncountable sentences and the Harnik–Makkai reduction

A set `K` of relational configurations on a carrier `V` is **minimally uncountable**
(`TauCeti.MinimallyUncountableOn`) when it meets uncountably many isomorphism classes and every cut
of `K` by an `L_{ω₁ω}` sentence has a side meeting only countably many isomorphism classes. For an
ordinal-valued rank `ρ`, `K` is **minimally unbounded** (`TauCeti.MinimallyUnboundedOn`) when `ρ`
is unbounded below `ω₁` on `K` and every sentence cut has a side on which `ρ` is bounded below
`ω₁`. For an infinitary sentence `φ`, `TauCeti.MinimallyUncountable` and
`TauCeti.MinimallyUnbounded` specialize these notions to `modelsOf (V := ℕ) φ`.

On any back-and-forth scattered set `K` of configurations on `ℕ`, an isolating rank is bounded below
`ω₁` precisely when `K` meets countably many isomorphism classes
(`TauCeti.IsIsolatingRank.countable_isoClasses_iff_bounded`), so minimal uncountability coincides
with minimal unboundedness for every isolating rank
(`TauCeti.IsIsolatingRank.minimallyUncountableOn_iff_minimallyUnboundedOn`), and minimal
unboundedness does not depend on the choice of isolating rank
(`TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`). Combining sentence-cut class selection
(`TauCeti.concentratedAtBFLevels_of_bfScattered_of_sentence_splits`) with sentence splits of
concentrated classes (`TauCeti.ConcentratedAtBFLevels.countable_isoClasses_inter_modelsOf_or_sdiff`)
identifies scattered minimally uncountable classes with uncountable classes concentrated at
back-and-forth levels (`TauCeti.bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels`).

In a countable relational vocabulary, every sentence cut of a minimally uncountable class has a side
meeting countably many isomorphism classes, so the class is thin
(`TauCeti.MinimallyUncountableOn.isThinOn`) and, when Borel, back-and-forth scattered
(`TauCeti.MinimallyUncountableOn.bfScattered`). The scatteredness hypotheses above can then be
dropped for Borel classes: a Borel class is minimally uncountable precisely when it is concentrated
at back-and-forth levels and meets uncountably many isomorphism classes
(`TauCeti.minimallyUncountableOn_iff_concentratedAtBFLevels`), or precisely when it is scattered and
minimally unbounded for some, equivalently every, isolating rank
(`TauCeti.IsIsolatingRank.minimallyUncountableOn_iff_bfScattered_and_minimallyUnboundedOn`).

The main result is the **Harnik–Makkai reduction**
(`TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`): in a countable relational vocabulary,
if `Θ` is an `L_{ω₁ω}` sentence whose model class on `ℕ` is back-and-forth scattered and meets
uncountably many isomorphism classes, then some strengthening `Θ ⊓ θ` is minimally uncountable.
More generally, any back-and-forth scattered set `K` of configurations on `ℕ` meeting uncountably
many isomorphism classes admits an `L_{ω₁ω}` sentence `θ` with `K ∩ modelsOf θ` minimally
uncountable whenever `K` is closed under some countable back-and-forth level
(`TauCeti.BFScattered.exists_minimallyUncountableOn_inter_modelsOf`), in particular whenever `K` is
isomorphism-invariant and Borel
(`TauCeti.BFScattered.exists_minimallyUncountableOn_inter_modelsOf_of_measurableSet`) or the model
class of a countably branching infinitary sentence
(`TauCeti.exists_minimallyUncountableOn_modelsOf_inter_of_bfScattered`).

Consequently, every counterexample `Θ` to Vaught's dichotomy has a scattered minimally uncountable
strengthening `Θ ⊓ θ` (`TauCeti.exists_minimallyUncountable_inf_of_not_hasVaughtDichotomy`), while
conversely a minimally uncountable sentence `φ` makes `φ ⊓ L.infiniteSentence` a counterexample
(`TauCeti.MinimallyUncountable.not_hasVaughtDichotomy_inf_infiniteSentence`). Hence
`VaughtConjecture` is equivalent to the absence of minimally uncountable sentences
(`TauCeti.vaughtConjecture_iff_forall_not_minimallyUncountableOn`), and to the absence of
scattered minimally uncountable—or scattered minimally unbounded—sentences
(`TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn`,
`TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn`).

## Main definitions

* `TauCeti.MinimallyUncountableOn`: a set of configurations meeting uncountably many isomorphism
  classes whose every `L_{ω₁ω}` sentence cut has a countable side.
* `TauCeti.MinimallyUnboundedOn`: rank-based counterpart using `TauCeti.UnboundedRankOn` and
  `TauCeti.BoundedRankOn`.
* `TauCeti.MinimallyUncountable` and `TauCeti.MinimallyUnbounded`: specializations to
  `modelsOf (V := ℕ) φ` for an infinitary sentence `φ`.

## Main results

* `TauCeti.MinimallyUncountableOn.exists_bfClass` and `TauCeti.MinimallyUnboundedOn.exists_bfClass`:
  existence, minimality, and uniqueness up to `bfEquivSetoid L V α` of the large class at a
  countable level with countably many classes.
* `TauCeti.IsIsolatingRank.minimallyUncountableOn_iff_minimallyUnboundedOn` and
  `TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`: agreement of minimal uncountability and
  minimal unboundedness on scattered sets, and independence of the isolating rank.
* `TauCeti.MinimallyUncountableOn.isThinOn` and `TauCeti.MinimallyUncountableOn.bfScattered`:
  minimally uncountable classes are thin, and back-and-forth scattered when Borel.
* `TauCeti.bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels`,
  `TauCeti.minimallyUncountableOn_iff_concentratedAtBFLevels`, and
  `TauCeti.minimallyUncountable_iff_concentratedAtBFLevels`: characterization via concentration at
  back-and-forth levels.
* `TauCeti.BFScattered.exists_minimallyUncountableOn_inter_modelsOf` and
  `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`: **the Harnik–Makkai reduction** to
  minimally uncountable counterexamples.
* `TauCeti.not_vaughtConjecture_of_minimallyUncountableOn` and
  `TauCeti.vaughtConjecture_iff_forall_not_minimallyUncountableOn`: a minimally uncountable sentence
  refutes `TauCeti.VaughtConjecture`, and the conjecture holds precisely when there is none.
* `TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`,
  `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn`, and
  `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn`: minimal-counterexample
  criteria and reformulations for `TauCeti.VaughtConjecture`.

## References

* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proceedings of
  the American Mathematical Society 67 (1977), 309–314.
* John R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689,
  Springer, 1978, 193–208.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII, §XII.2 (Definition XII.4, Lemmas XII.5–XII.6, Theorem XII.7,
  and Lemma XII.8).
* The definitions of `MinimallyUncountableOn` and `MinimallyUnboundedOn`, their equivalence on
  scattered classes, and the concentration and canonical large-class characterizations adapt
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean`,
  `InfinitaryLogic/Descriptive/MinimallyUnbounded.lean`, and
  `InfinitaryLogic/Conditional/MinimallyUncountableHeadline.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), generalized here to arbitrary relational languages, arbitrary isolating ranks, and
  arbitrary carriers where appropriate. The splitting-tree construction, the Harnik–Makkai
  reduction, and the Vaught-conjecture reformulations are new formalizations.
-/

public section

universe u v w o r uι

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Ordinal Set

namespace TauCeti

open RelationalConfiguration

/-! ### Minimally uncountable classes of configurations -/

section MinimallyUncountableOn

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
  {A K : Set (RelationalConfiguration L V)}

/-- A set `K` of configurations on `V` is **minimally uncountable** when it meets uncountably many
isomorphism classes and every cut of `K` by an `L_{ω₁ω}` sentence has a side meeting only countably
many isomorphism classes. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L V)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
    ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable

/-- Unfolding lemma for `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff :
    MinimallyUncountableOn K ↔
      ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
        ∀ θ : L.Sentenceω,
          (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
            (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- A minimally uncountable set meets uncountably many isomorphism classes. -/
theorem MinimallyUncountableOn.not_countable_image (h : MinimallyUncountableOn K) :
    ¬ (Quotient.mk (isoSetoid L V) '' K).Countable :=
  h.1

/-- The isomorphism quotient restricted to a minimally uncountable set is not countable. -/
theorem MinimallyUncountableOn.not_countable_quotient (h : MinimallyUncountableOn K) :
    ¬ Countable (Quotient ((isoSetoid L V).comap (Subtype.val : K → _))) :=
  Setoid.countable_quotient_comap_val_iff.not.mpr h.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally uncountable set has a side meeting countably many
isomorphism classes. -/
theorem MinimallyUncountableOn.countable_inter_or_sdiff (h : MinimallyUncountableOn K)
    (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  h.2 θ

/-- The empty set of configurations is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L V)) := by
  intro h
  exact h.1 (by simp)

/-- Every minimally uncountable set is nonempty. -/
theorem MinimallyUncountableOn.nonempty (h : MinimallyUncountableOn K) : K.Nonempty := by
  rw [← ne_empty_iff_nonempty]
  rintro rfl
  exact not_minimallyUncountableOn_empty h

/-- Any subset of a minimally uncountable set that still meets uncountably many isomorphism classes
is itself minimally uncountable. -/
theorem MinimallyUncountableOn.of_subset (hK : MinimallyUncountableOn K) (hAK : A ⊆ K)
    (hA : ¬ (Quotient.mk (isoSetoid L V) '' A).Countable) : MinimallyUncountableOn A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (image_mono (inter_subset_inter_left _ hAK)))
    (fun h => h.mono (image_mono (sdiff_le_sdiff_right hAK)))⟩

/-- Below `ω₁`, in a countable relational vocabulary on a countable carrier, every cut of a
minimally uncountable set by a back-and-forth level class has a countable side. -/
theorem MinimallyUncountableOn.countable_inter_bfEquivSetoid_or_sdiff
    [Countable (Σ n, L.Relations n)] [Countable V] (hK : MinimallyUncountableOn K)
    (c : RelationalConfiguration L V) {α : Ordinal.{o}} (hα : α < ω₁) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ {d | bfEquivSetoid L V α c d})).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable := by
  simpa only [modelsOf_scottSentenceAtLevel c hα] using hK.2 (c.scottSentenceAtLevel α)

/-- **Canonical large class at a countable level.** Below `ω₁`, if `K` is minimally uncountable and
meets only countably many level-`α` classes, then there is `c ∈ K` whose level-`α` trace in `K` is
minimally uncountable, whose complement in `K` meets countably many isomorphism classes, and which
is unique up to `bfEquivSetoid L V α` among all configurations with uncountable level-`α` trace in
`K`. -/
theorem MinimallyUncountableOn.exists_bfClass [Countable (Σ n, L.Relations n)] [Countable V]
    (hK : MinimallyUncountableOn K) {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      MinimallyUncountableOn (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable ∧
      ∀ c', ¬ (Quotient.mk (isoSetoid L V) '' (K ∩ {d | bfEquivSetoid L V α c' d})).Countable →
        bfEquivSetoid L V α c c' := by
  obtain ⟨c, hcK, hunc, hcount⟩ :=
    exists_bfClass_uncountable_isoClasses_and_countable_sdiff hK.1 hK.2 hα
  refine ⟨c, hcK, hK.of_subset inter_subset_left hunc, hcount, fun c' hc' => ?_⟩
  by_contra hnot
  have hsub : K ∩ {d | bfEquivSetoid L V α c' d} ⊆ K \ {d | bfEquivSetoid L V α c d} :=
    fun d ⟨hdK, hc'd⟩ =>
      ⟨hdK, fun hcd => hnot ((bfEquivSetoid L V α).trans' hcd ((bfEquivSetoid L V α).symm' hc'd))⟩
  exact hc' (hcount.mono (image_mono hsub))

end MinimallyUncountableOn

/-! ### Minimally unbounded classes of configurations -/

section MinimallyUnboundedOn

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
  {ρ : RelationalConfiguration L V → Ordinal.{r}} {A K : Set (RelationalConfiguration L V)}

/-- A set `K` of configurations on `V` is **minimally unbounded** with respect to an ordinal-valued
rank `ρ` when `ρ` is unbounded below `ω₁` on `K` and every cut of `K` by an `L_{ω₁ω}` sentence has
a side on which `ρ` is bounded below `ω₁`. -/
def MinimallyUnboundedOn (ρ : RelationalConfiguration L V → Ordinal.{r})
    (K : Set (RelationalConfiguration L V)) : Prop :=
  UnboundedRankOn ρ K ∧
    ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ)

/-- Unfolding lemma for `TauCeti.MinimallyUnboundedOn`. -/
theorem minimallyUnboundedOn_iff :
    MinimallyUnboundedOn ρ K ↔
      UnboundedRankOn ρ K ∧
        ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  Iff.rfl

/-- A minimally unbounded set has rank unbounded below `ω₁`. -/
theorem MinimallyUnboundedOn.unboundedRankOn (h : MinimallyUnboundedOn ρ K) :
    UnboundedRankOn ρ K :=
  h.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally unbounded set has a rank-bounded side. -/
theorem MinimallyUnboundedOn.boundedRankOn_inter_or_sdiff (h : MinimallyUnboundedOn ρ K)
    (θ : L.Sentenceω) :
    BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  h.2 θ

/-- The empty set of configurations is not minimally unbounded for any rank. -/
@[simp]
theorem not_minimallyUnboundedOn_empty (ρ : RelationalConfiguration L V → Ordinal.{r}) :
    ¬ MinimallyUnboundedOn ρ ∅ := fun h => not_unboundedRankOn_empty ρ h.1

/-- Every minimally unbounded set is nonempty. -/
theorem MinimallyUnboundedOn.nonempty (h : MinimallyUnboundedOn ρ K) : K.Nonempty := by
  rw [← ne_empty_iff_nonempty]
  rintro rfl
  exact not_minimallyUnboundedOn_empty ρ h

/-- Any rank-unbounded subset of a minimally unbounded set is itself minimally unbounded. -/
theorem MinimallyUnboundedOn.of_subset (hK : MinimallyUnboundedOn ρ K) (hAK : A ⊆ K)
    (hA : UnboundedRankOn ρ A) : MinimallyUnboundedOn ρ A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (inter_subset_inter_left _ hAK))
    (fun h => h.mono (sdiff_le_sdiff_right hAK))⟩

/-- Below `ω₁`, in a countable relational vocabulary on a countable carrier, every cut of a
minimally unbounded set by a back-and-forth level class has a rank-bounded side. -/
theorem MinimallyUnboundedOn.boundedRankOn_inter_bfEquivSetoid_or_sdiff
    [Countable (Σ n, L.Relations n)] [Countable V] (hK : MinimallyUnboundedOn ρ K)
    (c : RelationalConfiguration L V) {α : Ordinal.{o}} (hα : α < ω₁) :
    BoundedRankOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∨
      BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) := by
  simpa only [modelsOf_scottSentenceAtLevel c hα] using hK.2 (c.scottSentenceAtLevel α)

/-- **Canonical rank-unbounded class at a countable level.** Below `ω₁`, if `K` is minimally
unbounded for `ρ` and meets only countably many level-`α` classes, then there is `c ∈ K` whose
level-`α` trace in `K` is minimally unbounded for `ρ`, whose complement in `K` is rank-bounded,
and which is unique up to `bfEquivSetoid L V α` among all configurations with rank-unbounded
level-`α` trace in `K`. -/
theorem MinimallyUnboundedOn.exists_bfClass [Countable (Σ n, L.Relations n)] [Countable V]
    (hK : MinimallyUnboundedOn ρ K) {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      MinimallyUnboundedOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) ∧
      ∀ c', UnboundedRankOn ρ (K ∩ {d | bfEquivSetoid L V α c' d}) →
        bfEquivSetoid L V α c c' := by
  obtain ⟨c, hcK, hunb, hbound⟩ :=
    exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff hK.1 hK.2 hα
  refine ⟨c, hcK, hK.of_subset inter_subset_left hunb, hbound, fun c' hc' => ?_⟩
  by_contra hnot
  refine unboundedRankOn_iff_not_boundedRankOn.mp hc'
    (hbound.mono fun d ⟨hdK, hc'd⟩ => ⟨hdK, fun hcd => hnot ?_⟩)
  exact (bfEquivSetoid L V α).trans' hcd ((bfEquivSetoid L V α).symm' hc'd)

end MinimallyUnboundedOn

/-! ### Sentence-level predicates -/

section SentencePredicates

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}

/-- An infinitary sentence `φ` is **minimally uncountable** when its model class on `ℕ` is minimally
uncountable: `φ` has uncountably many models on `ℕ` up to isomorphism, and every `L_{ω₁ω}` sentence
cut of its models on `ℕ` has a countable side up to isomorphism. -/
def MinimallyUncountable (φ : L.SentenceInf ι) : Prop :=
  MinimallyUncountableOn (modelsOf (V := ℕ) φ)

/-- Sentence minimal uncountability is minimal uncountability of `modelsOf (V := ℕ) φ`. -/
theorem minimallyUncountable_def {φ : L.SentenceInf ι} :
    MinimallyUncountable φ ↔ MinimallyUncountableOn (modelsOf (V := ℕ) φ) :=
  Iff.rfl

/-- Characterization of `MinimallyUncountable` for an `L_{ω₁ω}` sentence `φ` through restricted
isomorphism quotients of `φ ⊓ θ` and `φ ⊓ θ.not` on `ℕ`. -/
theorem minimallyUncountable_iff {φ : L.Sentenceω} :
    MinimallyUncountable φ ↔
      ¬ Countable (Quotient (isoSetoidOn ℕ φ)) ∧
        ∀ θ : L.Sentenceω,
          Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
            Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not))) := by
  simp only [MinimallyUncountable, MinimallyUncountableOn, isoSetoidOn,
    Setoid.countable_quotient_comap_val_iff, modelsOf_inf, modelsOf_not, sdiff_eq]

/-- Conjoining `infiniteSentence` does not change minimal uncountability on `ℕ`. -/
@[simp]
theorem minimallyUncountable_inf_infiniteSentence_iff (φ : L.Sentenceω) :
    MinimallyUncountable (φ ⊓ L.infiniteSentence) ↔ MinimallyUncountable φ := by
  simp [MinimallyUncountable]

/-- An infinitary sentence `φ` is **minimally unbounded** with respect to a rank `ρ` on
configurations on `ℕ` when `modelsOf (V := ℕ) φ` is minimally unbounded for `ρ`. -/
def MinimallyUnbounded (ρ : RelationalConfiguration L ℕ → Ordinal.{r}) (φ : L.SentenceInf ι) :
    Prop :=
  MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ)

/-- Sentence minimal unboundedness is minimal unboundedness of `modelsOf (V := ℕ) φ`. -/
theorem minimallyUnbounded_def {ρ : RelationalConfiguration L ℕ → Ordinal.{r}}
    {φ : L.SentenceInf ι} :
    MinimallyUnbounded ρ φ ↔ MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ) :=
  Iff.rfl

/-- Characterization of `MinimallyUnbounded` for an `L_{ω₁ω}` sentence `φ` through `φ ⊓ θ` and
`φ ⊓ θ.not` on `ℕ`. -/
theorem minimallyUnbounded_iff {ρ : RelationalConfiguration L ℕ → Ordinal.{r}} {φ : L.Sentenceω} :
    MinimallyUnbounded ρ φ ↔
      UnboundedRankOn ρ (modelsOf (V := ℕ) φ) ∧
        ∀ θ : L.Sentenceω,
          BoundedRankOn ρ (modelsOf (V := ℕ) (φ ⊓ θ)) ∨
            BoundedRankOn ρ (modelsOf (V := ℕ) (φ ⊓ θ.not)) := by
  simp only [MinimallyUnbounded, MinimallyUnboundedOn, modelsOf_inf, modelsOf_not, sdiff_eq]

/-- Conjoining `infiniteSentence` does not change minimal unboundedness on `ℕ`. -/
@[simp]
theorem minimallyUnbounded_inf_infiniteSentence_iff
    (ρ : RelationalConfiguration L ℕ → Ordinal.{r}) (φ : L.Sentenceω) :
    MinimallyUnbounded ρ (φ ⊓ L.infiniteSentence) ↔ MinimallyUnbounded ρ φ := by
  simp [MinimallyUnbounded]

end SentencePredicates

/-! ### Equivalence on scattered classes and concentration -/

section ScatteredAndConcentrated

variable {L : Language.{u, v}} [L.IsRelational] {ι : Type uι}
  {K C : Set (RelationalConfiguration L ℕ)}

namespace IsIsolatingRank

variable {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- **Minimal uncountability and minimal unboundedness agree on scattered classes.** On any
back-and-forth scattered set `K`, `MinimallyUncountableOn K` is equivalent to
`MinimallyUnboundedOn ρ K` for every isolating rank `ρ`. -/
theorem minimallyUncountableOn_iff_minimallyUnboundedOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    MinimallyUncountableOn K ↔ MinimallyUnboundedOn ρ K := by
  refine and_congr
    ((not_congr (hρ.countable_image_iff_boundedRankOn hK)).trans
      unboundedRankOn_iff_not_boundedRankOn.symm)
    (forall_congr' fun θ => ?_)
  exact or_congr (hρ.countable_image_iff_boundedRankOn (hK.mono inter_subset_left))
    (hρ.countable_image_iff_boundedRankOn (hK.mono sdiff_subset))

/-- **Rank-independence of minimal unboundedness on scattered classes.** On a back-and-forth
scattered set, minimal unboundedness does not depend on which isolating rank is used. -/
theorem minimallyUnboundedOn_iff (hρ : IsIsolatingRank ρ) (hσ : IsIsolatingRank σ)
    (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn σ K :=
  (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hK).symm.trans
    (hσ.minimallyUncountableOn_iff_minimallyUnboundedOn hK)

end IsIsolatingRank

/-- A concentrated class meeting uncountably many isomorphism classes is minimally uncountable,
since every sentence cut of a concentrated class has a side meeting countably many isomorphism
classes. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn (hC : ConcentratedAtBFLevels C)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' C).Countable) :
    MinimallyUncountableOn C := by
  refine ⟨hunc, fun θ => ?_⟩
  simpa only [Setoid.countable_quotient_comap_val_iff] using
    hC.countable_isoClasses_inter_modelsOf_or_sdiff θ

/-- A back-and-forth scattered minimally uncountable class is concentrated at back-and-forth
levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    (h : MinimallyUncountableOn K) (hK : BFScattered K) : ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK h.2

/-- **Characterization of scattered minimally uncountable classes.** In a countable relational
vocabulary, a set `K` of configurations on `ℕ` is back-and-forth scattered and minimally
uncountable precisely when `K` is concentrated at back-and-forth levels and meets uncountably many
isomorphism classes. -/
theorem bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels
    [Countable (Σ n, L.Relations n)] :
    BFScattered K ∧ MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun ⟨hscat, hmin⟩ => ⟨hmin.concentratedAtBFLevels hscat, hmin.1⟩,
    fun ⟨hconc, hunc⟩ => ⟨hconc.bfScattered, hconc.minimallyUncountableOn hunc⟩⟩

/-- **Characterization of scattered minimally unbounded classes.** For a set `K` of configurations
on `ℕ` and any isolating rank `ρ`, `K` is back-and-forth scattered and minimally unbounded for `ρ`
precisely when `K` is concentrated at back-and-forth levels and meets uncountably many isomorphism
classes. -/
theorem bfScattered_and_minimallyUnboundedOn_iff_concentratedAtBFLevels
    [Countable (Σ n, L.Relations n)] {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) :
    BFScattered K ∧ MinimallyUnboundedOn ρ K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable := by
  rw [← bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels]
  exact and_congr_right fun hK => (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hK).symm

/-- For an infinitary sentence `φ` in a countable relational vocabulary, `φ` has scattered
minimally uncountable models on `ℕ` precisely when its models on `ℕ` are concentrated at
back-and-forth levels and uncountably many up to isomorphism. -/
theorem bfScattered_modelsOf_and_minimallyUncountable_iff [Countable (Σ n, L.Relations n)]
    (φ : L.SentenceInf ι) :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUncountable φ ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [minimallyUncountable_def,
    bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels,
    isoSetoidOn, Setoid.countable_quotient_comap_val_iff]

/-- For an infinitary sentence `φ` and isolating rank `ρ`, `φ` has scattered minimally unbounded
models on `ℕ` precisely when its models on `ℕ` are concentrated at back-and-forth levels and
uncountably many up to isomorphism. -/
theorem bfScattered_modelsOf_and_minimallyUnbounded_iff [Countable (Σ n, L.Relations n)]
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (φ : L.SentenceInf ι) :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUnbounded ρ φ ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [minimallyUnbounded_def,
    bfScattered_and_minimallyUnboundedOn_iff_concentratedAtBFLevels hρ,
    isoSetoidOn, Setoid.countable_quotient_comap_val_iff]

/-- For a thin sentence on `ℕ` with countable branching, minimal uncountability coincides with
minimal unboundedness for every isolating rank. -/
theorem IsThinOnNatModels.minimallyUncountable_iff_minimallyUnbounded
    [Countable (Σ n, L.Relations n)] [Countable ι] {φ : L.SentenceInf ι}
    (hthin : IsThinOnNatModels φ) {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) :
    MinimallyUncountable φ ↔ MinimallyUnbounded ρ φ :=
  hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hthin.bfScattered_modelsOf

end ScatteredAndConcentrated

/-! ### Minimally uncountable classes are thin -/

section Thin

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
  {ι : Type uι}

/-- **Minimally uncountable classes are thin.** In a countable relational vocabulary, a minimally
uncountable set of configurations on a countable carrier contains no nonempty perfect set of
pairwise non-isomorphic configurations. Neither measurability nor isomorphism invariance of `K` is
assumed. -/
theorem MinimallyUncountableOn.isThinOn {V : Type w} [Countable V]
    {K : Set (RelationalConfiguration L V)} (h : MinimallyUncountableOn K) :
    (isoSetoid L V).IsThinOn K :=
  isThinOn_of_sentence_splits h.countable_inter_or_sdiff

/-- A minimally uncountable infinitary sentence in a countable relational vocabulary is thin on
`ℕ`. -/
theorem MinimallyUncountable.isThinOnNatModels {φ : L.SentenceInf ι}
    (h : MinimallyUncountable φ) : IsThinOnNatModels φ :=
  isThinOnNatModels_iff_isThinOn.2 (minimallyUncountable_def.1 h).isThinOn

/-- In a countable relational vocabulary, a Borel minimally uncountable set of configurations on
`ℕ` is back-and-forth scattered. -/
theorem MinimallyUncountableOn.bfScattered {K : Set (RelationalConfiguration L ℕ)}
    (h : MinimallyUncountableOn K) (hK : MeasurableSet K) : BFScattered K :=
  BFScattered.of_isThinOn hK h.isThinOn

/-- A minimally uncountable infinitary sentence with countable branching in a countable relational
vocabulary has back-and-forth scattered models on `ℕ`. -/
theorem MinimallyUncountable.bfScattered_modelsOf [Countable ι] {φ : L.SentenceInf ι}
    (h : MinimallyUncountable φ) : BFScattered (modelsOf (V := ℕ) φ) :=
  (minimallyUncountable_def.1 h).bfScattered (measurableSet_modelsOf φ)

/-- **Characterization of Borel minimally uncountable classes.** In a countable relational
vocabulary, a Borel set `K` of configurations on `ℕ` is minimally uncountable precisely when it is
concentrated at back-and-forth levels and meets uncountably many isomorphism classes. -/
theorem minimallyUncountableOn_iff_concentratedAtBFLevels {K : Set (RelationalConfiguration L ℕ)}
    (hK : MeasurableSet K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable := by
  rw [← bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels]
  exact ⟨fun h => ⟨h.bfScattered hK, h⟩, And.right⟩

/-- **Characterization of minimally uncountable sentences.** In a countable relational vocabulary,
an infinitary sentence `φ` with countable branching is minimally uncountable precisely when its
models on `ℕ` are concentrated at back-and-forth levels and uncountably many up to isomorphism. -/
theorem minimallyUncountable_iff_concentratedAtBFLevels [Countable ι] (φ : L.SentenceInf ι) :
    MinimallyUncountable φ ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [minimallyUncountable_def, minimallyUncountableOn_iff_concentratedAtBFLevels
    (measurableSet_modelsOf φ), isoSetoidOn, Setoid.countable_quotient_comap_val_iff]

namespace IsIsolatingRank

variable {ρ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- **Minimal uncountability through an isolating rank.** In a countable relational vocabulary, a
Borel set `K` of configurations on `ℕ` is minimally uncountable precisely when it is back-and-forth
scattered and minimally unbounded for an isolating rank `ρ`. -/
theorem minimallyUncountableOn_iff_bfScattered_and_minimallyUnboundedOn (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : MeasurableSet K) :
    MinimallyUncountableOn K ↔ BFScattered K ∧ MinimallyUnboundedOn ρ K :=
  ⟨fun h => ⟨h.bfScattered hK,
      (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn (h.bfScattered hK)).1 h⟩,
    fun h => (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn h.1).2 h.2⟩

/-- In a countable relational vocabulary, an infinitary sentence `φ` with countable branching is
minimally uncountable precisely when its models on `ℕ` are back-and-forth scattered and `φ` is
minimally unbounded for an isolating rank `ρ`. -/
theorem minimallyUncountable_iff_bfScattered_and_minimallyUnbounded (hρ : IsIsolatingRank ρ)
    [Countable ι] (φ : L.SentenceInf ι) :
    MinimallyUncountable φ ↔ BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUnbounded ρ φ :=
  hρ.minimallyUncountableOn_iff_bfScattered_and_minimallyUnboundedOn (measurableSet_modelsOf φ)

end IsIsolatingRank

/-- **A minimally uncountable sentence is a Vaught counterexample.** In a countable relational
vocabulary, if `φ` is minimally uncountable, then `φ ⊓ L.infiniteSentence` fails Vaught's
witnessed dichotomy: it has uncountably many countable models up to isomorphism and no perfect set
of pairwise non-isomorphic ones. The conjunction with `L.infiniteSentence` discards the finite
models of `φ`, which may carry a perfect set. -/
theorem MinimallyUncountable.not_hasVaughtDichotomy_inf_infiniteSentence {φ : L.Sentenceω}
    (h : MinimallyUncountable φ) : ¬ HasVaughtDichotomy (φ ⊓ L.infiniteSentence) := by
  rw [hasVaughtDichotomy_inf_infiniteSentence_iff, not_or, ← isThinOnNatModels_iff]
  exact ⟨(minimallyUncountable_def.1 h).not_countable_quotient, h.isThinOnNatModels⟩

end Thin

/-! ### The Harnik–Makkai reduction -/

section HarnikMakkai

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

-- Assuming no sentence cut `K ∩ modelsOf θ` is minimally uncountable, we recursively build a
-- binary splitting tree along countable levels `α n < ω₁` with `α n + ω ≤ α (n + 1)`: each node's
-- `α n`-class is defined by `scottSentenceAtLevel` and splits into two uncountable sides, a common
-- level `α (n + 1)` saturates all `2 ^ n` splitting sentences (`exists_bfLevel_saturated_modelsOf`)
-- and selects uncountable child classes, and chain limits along Cantor branches (`ℕ → Bool`) embed
-- into the countable quotient of `K` at `⨆ n, α n < ω₁`.

/-- Finite stage `n` of the Harnik–Makkai binary splitting tree inside `K`: a countable level
`level < ω₁` and one configuration `node w` for each `w : Fin n → Bool` whose `level`-class lies in
`K` and meets uncountably many isomorphism classes. -/
private structure SplittingStage (L : Language.{u, v}) [L.IsRelational]
    (K : Set (RelationalConfiguration L ℕ)) (n : ℕ) where
  level : Ordinal.{0}
  level_lt : level < ω₁
  node : (Fin n → Bool) → RelationalConfiguration L ℕ
  class_subset : ∀ w {d : RelationalConfiguration L ℕ},
    bfEquivSetoid L ℕ level (node w) d → d ∈ K
  not_countable_class : ∀ w,
    ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ level (node w) d}).Countable

omit [Countable (Σ n, L.Relations n)] in
/-- Base stage `n = 0` of the splitting tree: when `K` is scattered, uncountable up to isomorphism,
and saturated at a countable level `α₀ < ω₁`, one `α₀`-class inside `K` meets uncountably many
isomorphism classes. -/
private theorem exists_splittingStage_zero {K : Set (RelationalConfiguration L ℕ)}
    (hK : BFScattered K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsat : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) :
    Nonempty (SplittingStage L K 0) := by
  have := hK.countable_quotient hα₀
  obtain ⟨a₀, ha₀K, ha₀_unc⟩ := (bfEquivSetoid L ℕ α₀).exists_class_not_countable_image hunc
  have hsub : {d | bfEquivSetoid L ℕ α₀ a₀ d} ⊆ K := fun d hd => hsat a₀ ha₀K d hd
  rw [inter_eq_self_of_subset_right hsub] at ha₀_unc
  exact ⟨⟨α₀, hα₀, fun _ => a₀, fun _ _ hd => hsub hd, fun _ => ha₀_unc⟩⟩

/-- One step of the Harnik–Makkai splitting tree: if no `K ∩ modelsOf θ` is minimally uncountable,
every node's class at stage `n` splits along a sentence into two uncountable sides, and one common
countable level `≥ s.level + ω` saturates all `2 ^ n` splitting sentences and selects uncountable
child classes. -/
private theorem SplittingStage.exists_step {K : Set (RelationalConfiguration L ℕ)} {n : ℕ}
    (s : SplittingStage L K n) (hK : BFScattered K)
    (hno_min : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (K ∩ modelsOf θ)) :
    ∃ s' : SplittingStage L K (n + 1),
      s.level + Ordinal.omega0 ≤ s'.level ∧
      (∀ u : Fin (n + 1) → Bool, bfEquivSetoid L ℕ s.level (s.node (Fin.init u)) (s'.node u)) ∧
      (∀ u v : Fin (n + 1) → Bool,
        Fin.init u = Fin.init v → u (Fin.last n) ≠ v (Fin.last n) →
          ¬ bfEquivSetoid L ℕ s'.level (s'.node u) (s'.node v)) := by
  classical
  -- Each node's level class is cut out by its Scott approximation sentence, so it splits into two
  -- uncountable sides along some sentence `φ w`.
  have hsplit (w : Fin n → Bool) : ∃ φ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) ''
        ({d | bfEquivSetoid L ℕ s.level (s.node w) d} ∩ modelsOf φ)).Countable ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) ''
        ({d | bfEquivSetoid L ℕ s.level (s.node w) d} \ modelsOf φ)).Countable := by
    have heq : K ∩ modelsOf ((s.node w).scottSentenceAtLevel s.level) =
        {d | bfEquivSetoid L ℕ s.level (s.node w) d} := by
      rw [modelsOf_scottSentenceAtLevel (s.node w) s.level_lt]
      exact inter_eq_self_of_subset_right fun _ hd => s.class_subset w hd
    have hnot := hno_min ((s.node w).scottSentenceAtLevel s.level)
    rw [heq, minimallyUncountableOn_iff, not_and, not_forall] at hnot
    obtain ⟨φ, hφ⟩ := hnot (s.not_countable_class w)
    exact ⟨φ, not_or.mp hφ⟩
  choose φ hφ_true hφ_false using hsplit
  -- Choose a single countable level `nextLevel ≥ s.level + ω` saturating every `φ w`.
  choose β hβ hsatφ using fun w =>
    exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) (φ w)
  let nextLevel : Ordinal.{0} := max (s.level + Ordinal.omega0) (⨆ w : Fin n → Bool, β w)
  have hnext_lt : nextLevel < ω₁ :=
    max_lt (Ordinal.isPrincipal_add_omega 1 s.level_lt Ordinal.omega0_lt_omega_one)
      (Ordinal.iSup_lt_omega_one hβ)
  have hstep_le : s.level + Ordinal.omega0 ≤ nextLevel := le_max_left _ _
  have hs_le : s.level ≤ nextLevel := le_self_add.trans hstep_le
  have hβ_le (w : Fin n → Bool) : β w ≤ nextLevel :=
    (Ordinal.le_iSup β w).trans (le_max_right _ _)
  -- On each side `b : Bool` of each node `w`, select an uncountable `nextLevel`-class.
  let side (w : Fin n → Bool) (b : Bool) : Set (RelationalConfiguration L ℕ) :=
    if b then {d | bfEquivSetoid L ℕ s.level (s.node w) d} ∩ modelsOf (φ w)
    else {d | bfEquivSetoid L ℕ s.level (s.node w) d} \ modelsOf (φ w)
  have hside_sub (w : Fin n → Bool) (b : Bool) :
      side w b ⊆ {d | bfEquivSetoid L ℕ s.level (s.node w) d} := by
    cases b
    · exact sdiff_subset
    · exact inter_subset_left
  have hside_K (w : Fin n → Bool) (b : Bool) : side w b ⊆ K :=
    (hside_sub w b).trans fun _ hd => s.class_subset w hd
  have hside_unc (w : Fin n → Bool) (b : Bool) :
      ¬ (Quotient.mk (isoSetoid L ℕ) '' side w b).Countable := by
    cases b
    · exact hφ_false w
    · exact hφ_true w
  have hside_sat (w : Fin n → Bool) (b : Bool) {c d : RelationalConfiguration L ℕ}
      (hc : c ∈ side w b) (hcd : bfEquivSetoid L ℕ nextLevel c d) : d ∈ side w b := by
    have hw_d : bfEquivSetoid L ℕ s.level (s.node w) d :=
      (bfEquivSetoid L ℕ s.level).trans' (hside_sub w b hc) (bfEquivSetoid_anti hs_le hcd)
    have hiff := hsatφ w nextLevel (hβ_le w) c d hcd
    cases b
    · exact ⟨hw_d, fun hd => hc.2 (hiff.mpr hd)⟩
    · exact ⟨hw_d, hiff.mp hc.2⟩
  have hchild (w : Fin n → Bool) (b : Bool) : ∃ c ∈ side w b,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ nextLevel c d}).Countable := by
    have := (hK.mono (hside_K w b)).countable_quotient hnext_lt
    obtain ⟨c, hc, hunc⟩ :=
      (bfEquivSetoid L ℕ nextLevel).exists_class_not_countable_image (hside_unc w b)
    have heq : side w b ∩ {d | bfEquivSetoid L ℕ nextLevel c d} =
        {d | bfEquivSetoid L ℕ nextLevel c d} :=
      inter_eq_self_of_subset_right fun d hd => hside_sat w b hc hd
    rw [heq] at hunc
    exact ⟨c, hc, hunc⟩
  choose child hchild_mem hchild_unc using hchild
  refine ⟨⟨nextLevel, hnext_lt, fun u => child (Fin.init u) (u (Fin.last n)),
    fun u _ hd => hside_K _ _ (hside_sat _ _ (hchild_mem _ _) hd),
    fun u => hchild_unc (Fin.init u) (u (Fin.last n))⟩, hstep_le,
    fun u => hside_sub _ _ (hchild_mem _ _), fun u v hinit hlast hbf => ?_⟩
  -- Sibling nodes lie on opposite sides of `modelsOf (φ (Fin.init u))`, which `nextLevel`
  -- separates.
  dsimp only at hbf
  rw [← hinit] at hbf
  have hu := hchild_mem (Fin.init u) (u (Fin.last n))
  have hv := hchild_mem (Fin.init u) (v (Fin.last n))
  cases hb₁ : u (Fin.last n) <;> cases hb₂ : v (Fin.last n)
  · exact hlast (hb₁.trans hb₂.symm)
  · rw [hb₁] at hu hbf
    rw [hb₂] at hv hbf
    exact hu.2 ((hsatφ (Fin.init u) nextLevel (hβ_le (Fin.init u)) _ _ hbf).mpr hv.2)
  · rw [hb₁] at hu hbf
    rw [hb₂] at hv hbf
    exact hv.2 ((hsatφ (Fin.init u) nextLevel (hβ_le (Fin.init u)) _ _ hbf).mp hu.2)
  · exact hlast (hb₁.trans hb₂.symm)

/-- **The Harnik–Makkai reduction for level-saturated scattered classes.** In a countable
relational vocabulary, if `K` is back-and-forth scattered, meets uncountably many isomorphism
classes, and is closed under `bfEquivSetoid L ℕ α₀` for some countable ordinal `α₀ < ω₁`, then some
`L_{ω₁ω}` sentence `θ` cuts out a minimally uncountable subset `K ∩ modelsOf θ`. -/
theorem BFScattered.exists_minimallyUncountableOn_inter_modelsOf
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsat : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (K ∩ modelsOf θ) := by
  classical
  by_contra! hno_min
  obtain ⟨s₀⟩ := exists_splittingStage_zero hK hunc hα₀ hsat
  let stage : ∀ n : ℕ, SplittingStage L K n :=
    Nat.rec s₀ fun _ s => (s.exists_step hK hno_min).choose
  have hstep (n : ℕ) := ((stage n).exists_step hK hno_min).choose_spec
  let α (n : ℕ) : Ordinal.{0} := (stage n).level
  have hα_step (n : ℕ) : α n + Ordinal.omega0 ≤ α (n + 1) := (hstep n).1
  have hα_mono : Monotone α := monotone_nat_of_le_succ fun n => le_self_add.trans (hα_step n)
  -- Follow each Cantor branch `X : ℕ → Bool` along the shifted nodes of length `i + 1`.
  let restr (n : ℕ) (X : ℕ → Bool) : Fin n → Bool := fun j => X j
  have hrestr_init (n : ℕ) (X : ℕ → Bool) : Fin.init (restr (n + 1) X) = restr n X := by
    funext j
    simp [Fin.init, restr]
  have hrestr_last (n : ℕ) (X : ℕ → Bool) : restr (n + 1) X (Fin.last n) = X n := by
    simp [restr]
  let chain (X : ℕ → Bool) (i : ℕ) : RelationalConfiguration L ℕ :=
    (stage (i + 1)).node (restr (i + 1) X)
  have hstep_node (X : ℕ → Bool) (n : ℕ) :
      bfEquivSetoid L ℕ (α n) ((stage n).node (restr n X)) (chain X n) := by
    have h := (hstep n).2.1 (restr (n + 1) X)
    rwa [hrestr_init] at h
  have hchain (X : ℕ → Bool) (i : ℕ) :
      bfEquivSetoid L ℕ (α i + Ordinal.omega0) (chain X i) (chain X (i + 1)) :=
    bfEquivSetoid_anti (hα_step i) (hstep_node X (i + 1))
  choose lim hlim using fun X => exists_limit_of_bfEquiv_chain hα_mono (hchain X)
  have hlim_node (X : ℕ → Bool) (n : ℕ) :
      bfEquivSetoid L ℕ (α n) ((stage n).node (restr n X)) (lim X) :=
    (bfEquivSetoid L ℕ (α n)).trans' (hstep_node X n)
      ((bfEquivSetoid L ℕ (α n)).symm' (hlim X n))
  have hlim_mem (X : ℕ → Bool) : lim X ∈ K :=
    (stage 0).class_subset (restr 0 X) (hlim_node X 0)
  -- Distinct branches separate at `β_sup := ⨆ n, α n < ω₁`, contradicting scatteredness of `K`.
  let β_sup : Ordinal.{0} := ⨆ n : ℕ, α n
  have hβ_lt : β_sup < ω₁ := Ordinal.iSup_lt_omega_one fun n => (stage n).level_lt
  have hsep {X Y : ℕ → Bool} (hXY : X ≠ Y) : ¬ bfEquivSetoid L ℕ β_sup (lim X) (lim Y) := by
    have hex : ∃ k, X k ≠ Y k := Function.ne_iff.mp hXY
    let i := Nat.find hex
    have hinit : Fin.init (restr (i + 1) X) = Fin.init (restr (i + 1) Y) := by
      rw [hrestr_init, hrestr_init]
      exact funext fun j => of_not_not (Nat.find_min hex j.isLt)
    have hlast : restr (i + 1) X (Fin.last i) ≠ restr (i + 1) Y (Fin.last i) := by
      rw [hrestr_last, hrestr_last]
      exact Nat.find_spec hex
    intro hbf
    have hbf' : bfEquivSetoid L ℕ (α (i + 1)) (lim X) (lim Y) :=
      bfEquivSetoid_anti (Ordinal.le_iSup α (i + 1)) hbf
    have hnodes : bfEquivSetoid L ℕ (α (i + 1)) (chain X i) (chain Y i) :=
      (bfEquivSetoid L ℕ (α (i + 1))).trans' (hlim_node X (i + 1))
        ((bfEquivSetoid L ℕ (α (i + 1))).trans' hbf'
          ((bfEquivSetoid L ℕ (α (i + 1))).symm' (hlim_node Y (i + 1))))
    exact (hstep i).2.2 (restr (i + 1) X) (restr (i + 1) Y) hinit hlast hnodes
  have hinj : Function.Injective
      (fun X : ℕ → Bool =>
        (⟦⟨lim X, hlim_mem X⟩⟧ :
          Quotient ((bfEquivSetoid L ℕ β_sup).comap (Subtype.val : K → _)))) :=
    fun X Y hEq => by_contra fun hXY =>
      hsep hXY (Quotient.exact (s := (bfEquivSetoid L ℕ β_sup).comap (Subtype.val : K → _)) hEq)
  have := hK.countable_quotient hβ_lt
  have hunc_cantor : ¬ Countable (ℕ → Bool) := by
    rw [← mk_le_aleph0_iff]
    simpa using aleph0_lt_continuum
  exact hunc_cantor hinj.countable

/-- **The Harnik–Makkai reduction for isomorphism-invariant Borel scattered classes.** Any
isomorphism-invariant Borel set `K` of configurations on `ℕ` that is back-and-forth scattered and
meets uncountably many isomorphism classes admits an `L_{ω₁ω}` sentence `θ` such that
`K ∩ modelsOf θ` is minimally uncountable. -/
theorem BFScattered.exists_minimallyUncountableOn_inter_modelsOf_of_measurableSet
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) (hBorel : MeasurableSet K)
    (hinv : IsomorphismInvariant K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (K ∩ modelsOf θ) := by
  have huniv : AnalyticSet (univ : Set (RelationalConfiguration L ℕ)) :=
    MeasurableSet.univ.analyticSet
  obtain ⟨α₀, hα₀, hsat⟩ :=
    exists_bfLevel_mem_iff_of_measurableSet.{u, v, 0, 0} huniv hBorel
      fun _ _ _ _ hcd => (hinv.mem_iff hcd).mp
  exact hK.exists_minimallyUncountableOn_inter_modelsOf hunc hα₀ fun c hc d hcd =>
    (hsat α₀ le_rfl c (mem_univ c) d (mem_univ d) hcd).mp hc

/-- If an infinitary sentence `Θ` with countable branching has back-and-forth scattered models on
`ℕ` meeting uncountably many isomorphism classes, some `L_{ω₁ω}` sentence `θ` cuts out a minimally
uncountable intersection `modelsOf Θ ∩ modelsOf θ`. -/
theorem exists_minimallyUncountableOn_modelsOf_inter_of_bfScattered {ι : Type uι} [Countable ι]
    {Θ : L.SentenceInf ι} (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) Θ ∩ modelsOf θ) :=
  hK.exists_minimallyUncountableOn_inter_modelsOf_of_measurableSet (measurableSet_modelsOf Θ)
    (isomorphismInvariant_modelsOf Θ) hunc

/-- **The Harnik–Makkai reduction.** In a countable relational vocabulary, any `L_{ω₁ω}` sentence
`Θ` whose models on `ℕ` are back-and-forth scattered and meet uncountably many isomorphism classes
has a minimally uncountable strengthening `Θ ⊓ θ`. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered {Θ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_modelsOf_inter_of_bfScattered hK hunc
  exact ⟨θ, by rwa [modelsOf_inf]⟩

/-- Sentence-level form of the Harnik–Makkai reduction: an `L_{ω₁ω}` sentence `Θ` whose models on
`ℕ` are back-and-forth scattered and uncountably many up to isomorphism has a strengthening `Θ ⊓ θ`
that is both back-and-forth scattered on `ℕ` and minimally uncountable (see
`exists_minimallyUncountableOn_modelsOf_inter_of_bfScattered` for intersections with arbitrary
countably branching infinitary sentences). -/
theorem exists_minimallyUncountable_inf_of_bfScattered {Θ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ Countable (Quotient (isoSetoidOn ℕ Θ))) :
    ∃ θ : L.Sentenceω,
      BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) ∧ MinimallyUncountable (Θ ⊓ θ) := by
  have hunc' : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable := by
    rwa [isoSetoidOn, Setoid.countable_quotient_comap_val_iff] at hunc
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hK hunc'
  exact ⟨θ, hK.mono (by simp), hθ⟩

/-- Every counterexample `Θ` to Vaught's witnessed dichotomy has a strengthening `Θ ⊓ θ` whose
models on `ℕ` are back-and-forth scattered and minimally uncountable. -/
theorem exists_minimallyUncountable_inf_of_not_hasVaughtDichotomy {Θ : L.Sentenceω}
    (hΘ : ¬ HasVaughtDichotomy Θ) :
    ∃ θ : L.Sentenceω,
      BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) ∧ MinimallyUncountable (Θ ⊓ θ) := by
  have hnot_perf : ¬ (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf Θ) :=
    fun hp => hΘ (hasVaughtDichotomy_of_nat (.inr hp))
  have hunc : ¬ Countable (Quotient (isoSetoidOn ℕ Θ)) :=
    fun hc => hΘ (hasVaughtDichotomy_of_nat (.inl hc))
  exact exists_minimallyUncountable_inf_of_bfScattered
    (BFScattered.of_isThinOn (measurableSet_modelsOf Θ) (Setoid.isThinOn_iff.mpr hnot_perf)) hunc

end HarnikMakkai

/-! ### Minimal-counterexample criteria for Vaught's conjecture -/

/-- **A minimally uncountable sentence refutes Vaught's conjecture.** If an `L_{ω₁ω}` sentence in a
countable relational language in universe zero has a minimally uncountable model class on `ℕ`, then
`VaughtConjecture` fails. -/
theorem not_vaughtConjecture_of_minimallyUncountableOn {L : Language.{0, 0}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω}
    (hmin : MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    ¬ VaughtConjecture := fun hv =>
  (minimallyUncountable_def.2 hmin).not_hasVaughtDichotomy_inf_infiniteSentence
    (vaughtConjecture_iff.1 hv L (φ ⊓ L.infiniteSentence))

/-- **Reduction of Vaught's conjecture to minimally uncountable sentences.** If no `L_{ω₁ω}`
sentence in a countable relational language in universe zero has a minimally uncountable model
class on `ℕ`, then `VaughtConjecture` holds. -/
theorem vaughtConjecture_of_forall_not_minimallyUncountableOn
    (h : ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
      (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    VaughtConjecture := by
  refine vaughtConjecture_iff_bfScattered.mpr fun L _ _ φ hscat => ?_
  by_contra hunc
  rw [isoSetoidOn, Setoid.countable_quotient_comap_val_iff] at hunc
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc
  exact h L (φ ⊓ θ) hθ

/-- **The minimally-uncountable formulation of Vaught's conjecture** (Harnik–Makkai; Steel).
`VaughtConjecture` holds precisely when no `L_{ω₁ω}` sentence in a countable relational language in
universe zero has a minimally uncountable model class on `ℕ`. No form of CH is assumed. -/
theorem vaughtConjecture_iff_forall_not_minimallyUncountableOn :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) :=
  ⟨fun hv _ _ _ _ hmin => not_vaughtConjecture_of_minimallyUncountableOn hmin hv,
    vaughtConjecture_of_forall_not_minimallyUncountableOn⟩

/-- **The scattered minimally-uncountable formulation of Vaught's conjecture.** `VaughtConjecture`
is equivalent, without CH, to the non-existence of a back-and-forth scattered minimally uncountable
`L_{ω₁ω}` sentence. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω),
        BFScattered (modelsOf (V := ℕ) φ) → ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) := by
  refine ⟨fun hv _ _ _ _ _ hmin =>
    not_vaughtConjecture_of_minimallyUncountableOn hmin hv, fun h => ?_⟩
  refine vaughtConjecture_iff_bfScattered.mpr fun L _ _ φ hscat => ?_
  by_contra hunc
  obtain ⟨θ, hθ_scat, hθ_min⟩ := exists_minimallyUncountable_inf_of_bfScattered hscat hunc
  exact h L (φ ⊓ θ) hθ_scat hθ_min

/-- **The minimally-unbounded formulation of Vaught's conjecture** (Montalbán). `VaughtConjecture`
is equivalent, without CH, to the non-existence of a back-and-forth scattered `L_{ω₁ω}` sentence
that is minimally unbounded with respect to an isolating rank. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω) (ρ : RelationalConfiguration L ℕ → Ordinal.{0}),
        IsIsolatingRank ρ → BFScattered (modelsOf (V := ℕ) φ) →
        ¬ MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ) := by
  rw [vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn]
  constructor
  · intro h L _ _ φ ρ hρ hscat hmin
    exact h L φ hscat ((hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hscat).mpr hmin)
  · intro h L _ _ φ hscat hmin
    exact h L φ _ (isIsolatingRank_scottHeight L) hscat
      ((isIsolatingRank_scottHeight L |>.minimallyUncountableOn_iff_minimallyUnboundedOn hscat).mp
        hmin)

/-- **The Scott-height minimally-unbounded formulation of Vaught's conjecture.** `VaughtConjecture`
holds precisely when no back-and-forth scattered `L_{ω₁ω}` sentence is minimally unbounded for the
external Scott height on `ℕ`. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn_scottHeight :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω),
        BFScattered (modelsOf (V := ℕ) φ) →
        ¬ MinimallyUnboundedOn (fun c => @scottHeight L _ ℕ c.toStructure)
          (modelsOf (V := ℕ) φ) := by
  rw [vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn]
  refine forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun φ => imp_congr_right fun hscat => not_congr ?_
  exact (isIsolatingRank_scottHeight L).minimallyUncountableOn_iff_minimallyUnboundedOn hscat

end TauCeti
