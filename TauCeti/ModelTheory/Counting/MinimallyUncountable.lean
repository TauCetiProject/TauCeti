/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Vaught

/-!
# Minimally uncountable classes and the Harnik–Makkai reduction

A class `K` of relational configurations is *minimally uncountable*
(`TauCeti.MinimallyUncountableOn`) when it meets uncountably many isomorphism classes, yet every cut
of `K` by an `L_{ω₁ω}` sentence has a side meeting only countably many. Relative to an
ordinal-valued rank `ρ`, `K` is *minimally unbounded* (`TauCeti.MinimallyUnboundedOn`) when `ρ` is
unbounded below `ω₁` on `K`, yet every `L_{ω₁ω}` sentence cut has a side on which `ρ` is strictly
bounded below `ω₁`.

On a back-and-forth scattered class on `ℕ`, countability of the isomorphism classes on any subset
coincides with strict boundedness below `ω₁` of any isolating rank. Minimal uncountability and
minimal unboundedness therefore coincide on scattered classes for every isolating rank, so minimal
unboundedness on a scattered class does not depend on which isolating rank is chosen. For an
`L_{ω₁ω}` sentence whose models on `ℕ` are scattered, minimal uncountability is also equivalent to
concentration at back-and-forth levels (`TauCeti.ConcentratedAtBFLevels`) together with meeting
uncountably many isomorphism classes.

The central theorem of this file is the **Harnik–Makkai reduction**
(`TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`, proved for arbitrary level-saturated
scattered classes in
`TauCeti.exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered_of_saturated`): every sentence
with back-and-forth scattered models on `ℕ` meeting uncountably many isomorphism classes has a
minimally uncountable strengthening `Θ ⊓ θ`. Assuming otherwise, one builds a full binary tree of
large back-and-forth classes inside `modelsOf Θ` at countable levels `α_n < ω₁` with
`α_n + ω ≤ α_{n+1}`, splitting each node's level class by a sentence into two large sides, raising
the level past the saturation ordinals of all `2^n` splitting sentences, and selecting a large
level-`α_{n+1}` class on each side so that sibling branches disagree at `α_{n+1}`. Passing to
back-and-forth chain limits along each branch `X : ℕ → Bool`
(`TauCeti.RelationalConfiguration.exists_limit_of_bfEquiv_chain`) injects Cantor space into the
countable level quotient at `⨆ n, α_n < ω₁`, contradicting scatteredness without invoking
continuity of the branch map or the continuum hypothesis.

Consequently, Vaught's perfect-set conjecture holds if and only if no sentence with scattered models
on `ℕ` is minimally uncountable (or minimally unbounded for an isolating rank), and if and only if
every sentence whose models on `ℕ` are concentrated at back-and-forth levels has countably many
models on `ℕ` up to isomorphism.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes, and every
  `L_{ω₁ω}` sentence cut of `K` has a side meeting countably many.
* `TauCeti.MinimallyUnboundedOn ρ K`: `ρ` is unbounded below `ω₁` on `K`, and every `L_{ω₁ω}`
  sentence cut of `K` has a side on which `ρ` is strictly bounded below `ω₁`.

## Main results

* `TauCeti.minimallyUncountableOn_modelsOf_iff_inf` and
  `TauCeti.minimallyUnboundedOn_modelsOf_iff_inf`: the sentence-conjunction forms for model classes.
* `TauCeti.MinimallyUncountableOn.exists_bfClass_minimallyUncountableOn_and_countable_sdiff` and
  `TauCeti.MinimallyUnboundedOn.exists_bfClass_minimallyUnboundedOn_and_boundedRankOn_sdiff`:
  selecting the unique large class at a countable back-and-forth level.
* `TauCeti.IsIsolatingRank.minimallyUncountableOn_iff_minimallyUnboundedOn` and
  `TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`: equivalence with minimal unboundedness and
  rank-independence on scattered classes.
* `TauCeti.bfScattered_and_minimallyUncountableOn_modelsOf_iff`: scattered minimally uncountable
  model classes are the concentrated ones meeting uncountably many isomorphism classes.
* `TauCeti.exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered_of_saturated` and
  `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`: the Harnik–Makkai reduction.
* `TauCeti.exists_bfScattered_and_minimallyUncountableOn_of_not_hasVaughtDichotomy`: reducing a
  counterexample to `HasVaughtDichotomy` to a scattered minimally uncountable strengthening.
* `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn`,
  `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn`, and
  `TauCeti.vaughtConjecture_iff_forall_concentratedAtBFLevels_countable`: minimal-counterexample and
  concentration formulations of Vaught's conjecture.

## References

* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proceedings of
  the American Mathematical Society 67 (1977), 309–314.
* John R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2 (Lemmas XII.5–XII.6 and Theorem XII.7).
* `MinimallyUncountableOn`, `MinimallyUnboundedOn`, and the scattered concentration equivalences
  adapt `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` and
  `InfinitaryLogic/Descriptive/MinimallyUnbounded.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`
  (Apache-2.0), generalized here to arbitrary carriers and arbitrary isolating ranks; the binary
  splitting tree and the Harnik–Makkai reduction are new work following Montalbán's §XII.2 in the
  one-element back-and-forth convention of `TauCeti.BFEquiv`.
-/

public section

universe u v w uι o r

open FirstOrder FirstOrder.Language Cardinal Ordinal MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

/-! ### Minimally uncountable classes -/

section MinimallyUncountableOn

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
variable {A K : Set (RelationalConfiguration L V)}

/-- A set `K` of configurations on `V` is **minimally uncountable** when it meets uncountably many
isomorphism classes, and every cut of `K` by an `L_{ω₁ω}` sentence has a side meeting only
countably many isomorphism classes. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L V)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
    ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable

/-- Unfolding characterization of `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff :
    MinimallyUncountableOn K ↔
      ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
        ∀ θ : L.Sentenceω,
          (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
            (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- The empty class is never minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L V)) := by
  simp [MinimallyUncountableOn]

/-- If `K` meets uncountably many isomorphism classes and is not minimally uncountable, some
`L_{ω₁ω}` sentence cuts `K` into two sides that both meet uncountably many isomorphism classes. -/
theorem exists_sentence_uncountable_inter_and_sdiff_of_not_minimallyUncountableOn
    (hunc : ¬ (Quotient.mk (isoSetoid L V) '' K).Countable)
    (hnot : ¬ MinimallyUncountableOn K) :
    ∃ θ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∧
        ¬ (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable := by
  rw [MinimallyUncountableOn] at hnot
  push Not at hnot
  exact hnot hunc

/-- Sentence-conjunction form of `MinimallyUncountableOn` on the model class of an `L_{ω₁ω}`
sentence `φ`: `φ` has uncountably many models on `V` up to isomorphism, and for every sentence `θ`
either `φ ⊓ θ` or `φ ⊓ θ.not` has countably many. -/
theorem minimallyUncountableOn_modelsOf_iff_inf (φ : L.Sentenceω) :
    MinimallyUncountableOn (modelsOf (V := V) φ) ↔
      ¬ Countable (Quotient (isoSetoidOn V φ)) ∧
        ∀ θ : L.Sentenceω, Countable (Quotient (isoSetoidOn V (φ ⊓ θ))) ∨
          Countable (Quotient (isoSetoidOn V (φ ⊓ θ.not))) := by
  simp only [MinimallyUncountableOn, isoSetoidOn, Setoid.countable_quotient_comap_val_iff,
    modelsOf_inf, modelsOf_not, sdiff_eq]

namespace MinimallyUncountableOn

/-- A minimally uncountable class meets uncountably many isomorphism classes. -/
theorem not_countable_isoClasses (hK : MinimallyUncountableOn K) :
    ¬ (Quotient.mk (isoSetoid L V) '' K).Countable :=
  hK.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally uncountable class has a side meeting countably many
isomorphism classes. -/
theorem countable_inter_or_sdiff (hK : MinimallyUncountableOn K) (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  hK.2 θ

/-- A minimally uncountable class is nonempty. -/
theorem nonempty (hK : MinimallyUncountableOn K) : K.Nonempty :=
  nonempty_iff_ne_empty.2 fun h => not_minimallyUncountableOn_empty (h ▸ hK)

/-- Any subset of a minimally uncountable class that still meets uncountably many isomorphism
classes is itself minimally uncountable. -/
theorem of_subset (hK : MinimallyUncountableOn K) (hAK : A ⊆ K)
    (hA : ¬ (Quotient.mk (isoSetoid L V) '' A).Countable) : MinimallyUncountableOn A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (image_mono (inter_subset_inter_left _ hAK)))
    (fun h => h.mono (image_mono (sdiff_le_sdiff_right hAK)))⟩

/-- Removing a complement `K \ B` that meets only countably many isomorphism classes leaves a
minimally uncountable intersection `K ∩ B`. -/
theorem inter_of_countable_sdiff (hK : MinimallyUncountableOn K)
    {B : Set (RelationalConfiguration L V)}
    (hdiff : (Quotient.mk (isoSetoid L V) '' (K \ B)).Countable) :
    MinimallyUncountableOn (K ∩ B) := by
  refine hK.of_subset inter_subset_left fun hinter => hK.1 ?_
  rw [← inter_union_sdiff K B, image_union]
  exact hinter.union hdiff

/-- Removing an intersection `K ∩ B` that meets only countably many isomorphism classes leaves a
minimally uncountable complement `K \ B`. -/
theorem sdiff_of_countable_inter (hK : MinimallyUncountableOn K)
    {B : Set (RelationalConfiguration L V)}
    (hinter : (Quotient.mk (isoSetoid L V) '' (K ∩ B)).Countable) :
    MinimallyUncountableOn (K \ B) := by
  refine hK.of_subset sdiff_subset fun hdiff => hK.1 ?_
  rw [← inter_union_sdiff K B, image_union]
  exact hinter.union hdiff

/-- If a minimally uncountable class on a countable carrier meets countably many classes at a
countable back-and-forth level `α`, one of its level-`α` classes is again minimally uncountable and
its complement in `K` meets only countably many isomorphism classes. -/
theorem exists_bfClass_minimallyUncountableOn_and_countable_sdiff
    [Countable (Σ n, L.Relations n)] [Countable V] (hK : MinimallyUncountableOn K)
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, MinimallyUncountableOn (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable := by
  obtain ⟨c, hcK, hunc, hdiff⟩ :=
    exists_bfClass_uncountable_isoClasses_and_countable_sdiff hK.1 hK.2 hα
  exact ⟨c, hcK, hK.of_subset inter_subset_left hunc, hdiff⟩

end MinimallyUncountableOn

end MinimallyUncountableOn

/-! ### Minimally unbounded classes -/

section MinimallyUnboundedOn

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
variable {ρ : RelationalConfiguration L V → Ordinal.{r}}
variable {A K : Set (RelationalConfiguration L V)}

/-- A set `K` of configurations on `V` is **minimally unbounded** for an ordinal-valued rank `ρ`
when `ρ` is unbounded below `ω₁` on `K`, and every cut of `K` by an `L_{ω₁ω}` sentence has a side
on which `ρ` is strictly bounded below `ω₁`. No invariance or isolation property of `ρ` is
assumed. -/
def MinimallyUnboundedOn (ρ : RelationalConfiguration L V → Ordinal.{r})
    (K : Set (RelationalConfiguration L V)) : Prop :=
  UnboundedRankOn ρ K ∧
    ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ)

/-- Unfolding characterization of `TauCeti.MinimallyUnboundedOn`. -/
theorem minimallyUnboundedOn_iff :
    MinimallyUnboundedOn ρ K ↔
      UnboundedRankOn ρ K ∧
        ∀ θ : L.Sentenceω,
          BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  Iff.rfl

/-- The empty class is never minimally unbounded. -/
@[simp]
theorem not_minimallyUnboundedOn_empty :
    ¬ MinimallyUnboundedOn ρ (∅ : Set (RelationalConfiguration L V)) := by
  simp [MinimallyUnboundedOn]

/-- Sentence-conjunction form of `MinimallyUnboundedOn` on the model class of an `L_{ω₁ω}` sentence
`φ`. -/
theorem minimallyUnboundedOn_modelsOf_iff_inf (φ : L.Sentenceω) :
    MinimallyUnboundedOn ρ (modelsOf (V := V) φ) ↔
      UnboundedRankOn ρ (modelsOf (V := V) φ) ∧
        ∀ θ : L.Sentenceω, BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ)) ∨
          BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ.not)) := by
  simp only [MinimallyUnboundedOn, modelsOf_inf, modelsOf_not, sdiff_eq]

namespace MinimallyUnboundedOn

/-- A minimally unbounded class is rank-unbounded below `ω₁`. -/
theorem unboundedRankOn (hK : MinimallyUnboundedOn ρ K) : UnboundedRankOn ρ K :=
  hK.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally unbounded class has a rank-bounded side. -/
theorem boundedRankOn_inter_or_sdiff (hK : MinimallyUnboundedOn ρ K) (θ : L.Sentenceω) :
    BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  hK.2 θ

/-- A minimally unbounded class is nonempty. -/
theorem nonempty (hK : MinimallyUnboundedOn ρ K) : K.Nonempty :=
  nonempty_iff_ne_empty.2 fun h => not_minimallyUnboundedOn_empty (h ▸ hK)

/-- Any rank-unbounded subset of a minimally unbounded class is itself minimally unbounded. -/
theorem of_subset (hK : MinimallyUnboundedOn ρ K) (hAK : A ⊆ K) (hA : UnboundedRankOn ρ A) :
    MinimallyUnboundedOn ρ A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (inter_subset_inter_left _ hAK))
    (fun h => h.mono (sdiff_le_sdiff_right hAK))⟩

/-- If `ρ` is bounded below `ω₁` on both `K ∩ B` and `K \ B`, then `ρ` is bounded below `ω₁` on
`K`. -/
private theorem boundedRankOn_of_inter_and_sdiff {α : Type*} {ρ : α → Ordinal.{r}} {K B : Set α}
    (hinter : BoundedRankOn ρ (K ∩ B)) (hdiff : BoundedRankOn ρ (K \ B)) :
    BoundedRankOn ρ K := by
  obtain ⟨β₁, hβ₁, hb₁⟩ := boundedRankOn_iff.1 hinter
  obtain ⟨β₂, hβ₂, hb₂⟩ := boundedRankOn_iff.1 hdiff
  refine boundedRankOn_iff.2 ⟨max β₁ β₂, max_lt hβ₁ hβ₂, fun x hx => ?_⟩
  by_cases hxB : x ∈ B
  · exact (hb₁ x ⟨hx, hxB⟩).trans_le (le_max_left _ _)
  · exact (hb₂ x ⟨hx, hxB⟩).trans_le (le_max_right _ _)

/-- Removing a rank-bounded complement `K \ B` leaves a minimally unbounded intersection `K ∩ B`. -/
theorem inter_of_boundedRankOn_sdiff (hK : MinimallyUnboundedOn ρ K)
    {B : Set (RelationalConfiguration L V)} (hdiff : BoundedRankOn ρ (K \ B)) :
    MinimallyUnboundedOn ρ (K ∩ B) :=
  hK.of_subset inter_subset_left <| unboundedRankOn_iff_not_boundedRankOn.2 fun hinter =>
    unboundedRankOn_iff_not_boundedRankOn.1 hK.1 (boundedRankOn_of_inter_and_sdiff hinter hdiff)

/-- Removing a rank-bounded intersection `K ∩ B` leaves a minimally unbounded complement `K \ B`. -/
theorem sdiff_of_boundedRankOn_inter (hK : MinimallyUnboundedOn ρ K)
    {B : Set (RelationalConfiguration L V)} (hinter : BoundedRankOn ρ (K ∩ B)) :
    MinimallyUnboundedOn ρ (K \ B) :=
  hK.of_subset sdiff_subset <| unboundedRankOn_iff_not_boundedRankOn.2 fun hdiff =>
    unboundedRankOn_iff_not_boundedRankOn.1 hK.1 (boundedRankOn_of_inter_and_sdiff hinter hdiff)

/-- If a minimally unbounded class on a countable carrier meets countably many classes at a
countable back-and-forth level `α`, one of its level-`α` classes is again minimally unbounded and
its complement in `K` is rank-bounded below `ω₁`. -/
theorem exists_bfClass_minimallyUnboundedOn_and_boundedRankOn_sdiff
    [Countable (Σ n, L.Relations n)] [Countable V] (hK : MinimallyUnboundedOn ρ K)
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, MinimallyUnboundedOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) := by
  obtain ⟨c, hcK, hunb, hdiff⟩ :=
    exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff hK.1 hK.2 hα
  exact ⟨c, hcK, hK.of_subset inter_subset_left hunb, hdiff⟩

end MinimallyUnboundedOn

end MinimallyUnboundedOn

/-! ### Scattered classes, isolating ranks, and concentration -/

section ScatteredAndConcentrated

variable {L : Language.{u, v}} [L.IsRelational]
variable {K : Set (RelationalConfiguration L ℕ)}

namespace IsIsolatingRank

variable {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- On a back-and-forth scattered set, countability of the isomorphism classes met by `K` is
equivalent to `BoundedRankOn ρ K`. -/
theorem countable_image_isoSetoid_iff_boundedRankOn (hρ : IsIsolatingRank ρ) (hK : BFScattered K) :
    (Quotient.mk (isoSetoid L ℕ) '' K).Countable ↔ BoundedRankOn ρ K :=
  Setoid.countable_quotient_comap_val_iff.symm.trans
    ((hρ.countable_isoClasses_iff_bounded hK).trans boundedRankOn_iff.symm)

/-- **Minimal uncountability is minimal unboundedness on scattered classes.** For any isolating
rank `ρ` and any back-and-forth scattered class `K` on `ℕ`, `K` is minimally uncountable if and
only if `K` is minimally unbounded for `ρ`. Neither definability of `K` nor countability of `L` is
needed. -/
theorem minimallyUncountableOn_iff_minimallyUnboundedOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    MinimallyUncountableOn K ↔ MinimallyUnboundedOn ρ K := by
  simp only [MinimallyUncountableOn, MinimallyUnboundedOn, unboundedRankOn_iff_not_boundedRankOn,
    hρ.countable_image_isoSetoid_iff_boundedRankOn hK]
  exact and_congr_right' <| forall_congr' fun θ => or_congr
    (hρ.countable_image_isoSetoid_iff_boundedRankOn (hK.mono inter_subset_left))
    (hρ.countable_image_isoSetoid_iff_boundedRankOn (hK.mono sdiff_subset))

/-- **Rank-independence of minimal unboundedness on scattered classes.** On a back-and-forth
scattered class `K` on `ℕ`, any two isolating ranks yield the same notion of minimal
unboundedness. -/
theorem minimallyUnboundedOn_iff (hρ : IsIsolatingRank ρ) (hσ : IsIsolatingRank σ)
    (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn σ K :=
  (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hK).symm.trans
    (hσ.minimallyUncountableOn_iff_minimallyUnboundedOn hK)

end IsIsolatingRank

/-- A back-and-forth scattered minimally uncountable class on `ℕ` in a countable relational
language is concentrated at back-and-forth levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels_of_bfScattered
    [Countable (Σ n, L.Relations n)] (hK : MinimallyUncountableOn K) (hscat : BFScattered K) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hscat hK.2

/-- An analytic class on `ℕ` that is concentrated at back-and-forth levels and meets uncountably
many isomorphism classes is minimally uncountable. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn_of_analyticSet
    [∀ n, Countable (L.Relations n)] (hconc : ConcentratedAtBFLevels K) (han : AnalyticSet K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    MinimallyUncountableOn K := by
  refine ⟨hunc, fun θ => ?_⟩
  simpa only [Setoid.countable_quotient_comap_val_iff] using
    hconc.countable_isoClasses_inter_modelsOf_or_sdiff han θ

/-- If the models on `ℕ` of a sentence with countable branching are concentrated at back-and-forth
levels and meet uncountably many isomorphism classes, its model class on `ℕ` is minimally
uncountable. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn_modelsOf
    [∀ n, Countable (L.Relations n)] {ι : Type uι} [Countable ι] {φ : L.SentenceInf ι}
    (hconc : ConcentratedAtBFLevels (modelsOf (V := ℕ) φ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) φ).Countable) :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) :=
  hconc.minimallyUncountableOn_of_analyticSet (measurableSet_modelsOf φ).analyticSet hunc

/-- **Concentration characterization for scattered sentences.** In a countable relational language,
the models on `ℕ` of an `L_{ω₁ω}` sentence `φ` are back-and-forth scattered and minimally
uncountable if and only if they are concentrated at back-and-forth levels and meet uncountably many
isomorphism classes. -/
theorem bfScattered_and_minimallyUncountableOn_modelsOf_iff
    [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω) :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) φ).Countable :=
  ⟨fun ⟨hscat, hmin⟩ => ⟨hmin.concentratedAtBFLevels_of_bfScattered hscat, hmin.1⟩,
    fun ⟨hconc, hunc⟩ => ⟨hconc.bfScattered, hconc.minimallyUncountableOn_modelsOf hunc⟩⟩

end ScatteredAndConcentrated

/-! ### The binary splitting tree and the Harnik–Makkai reduction -/

section SplittingTree

variable {L : Language.{u, v}} [L.IsRelational]

/-- If `S ⊆ K` meets uncountably many isomorphism classes, `K` is back-and-forth scattered, and `S`
is saturated in `RelationalConfiguration L ℕ` at a countable level `α < ω₁`, then some `c ∈ S` has
its entire level-`α` class contained in `S` and meeting uncountably many isomorphism classes. -/
private theorem exists_bfClass_subset_and_uncountable_of_saturated
    {K S : Set (RelationalConfiguration L ℕ)} (hscat : BFScattered K) (hSK : S ⊆ K)
    (hS : ¬ (Quotient.mk (isoSetoid L ℕ) '' S).Countable) {α : Ordinal.{0}} (hα : α < ω₁)
    (hsat : ∀ c ∈ S, ∀ d, bfEquivSetoid L ℕ α c d → d ∈ S) :
    ∃ c ∈ S, {d | bfEquivSetoid L ℕ α c d} ⊆ S ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ α c d}).Countable := by
  classical
  have := (hscat.mono hSK).countable_quotient hα
  let Q := Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : S → _))
  by_contra! hall
  refine hS ((countable_iUnion fun q : Q =>
    hall q.out.val q.out.prop (hsat q.out.val q.out.prop)).mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact mem_iUnion.2 ⟨⟦⟨x, hx⟩⟧, x,
    Quotient.exact (s := (bfEquivSetoid L ℕ α).comap (Subtype.val : S → _)) (Quotient.out_eq _),
    rfl⟩

/-- Stage `n` of the Harnik–Makkai binary splitting tree inside `K`: a countable level `level < ω₁`
and `2^n` configurations `node σ` whose level classes lie inside `K` and each meet uncountably many
isomorphism classes. -/
private structure TreeStage (K : Set (RelationalConfiguration L ℕ)) (n : ℕ) where
  level : Ordinal.{0}
  level_lt : level < ω₁
  node : (Fin n → Bool) → RelationalConfiguration L ℕ
  subset_target : ∀ σ, {d | bfEquivSetoid L ℕ level (node σ) d} ⊆ K
  uncountable_class :
    ∀ σ, ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ level (node σ) d}).Countable

/-- One inductive step of the Harnik–Makkai splitting tree: advances the countable level by at
least `ω`, preserves `s.level`-equivalence from each parent `Fin.init τ` to `τ`, and separates
sibling nodes differing at `Fin.last n` at the new level. -/
private structure SplittingStep (K : Set (RelationalConfiguration L ℕ)) {n : ℕ}
    (s : TreeStage K n) where
  next : TreeStage K (n + 1)
  level_step : s.level + Ordinal.omega0 ≤ next.level
  parent_equiv :
    ∀ τ : Fin (n + 1) → Bool, bfEquivSetoid L ℕ s.level (s.node (Fin.init τ)) (next.node τ)
  sibling_ne :
    ∀ τ₁ τ₂ : Fin (n + 1) → Bool, Fin.init τ₁ = Fin.init τ₂ →
      τ₁ (Fin.last n) ≠ τ₂ (Fin.last n) →
      ¬ bfEquivSetoid L ℕ next.level (next.node τ₁) (next.node τ₂)

/-- The root stage (`n = 0`) of the splitting tree, built from a countable saturation level `α₀` of
`K`. -/
private noncomputable def treeStageZero {K : Set (RelationalConfiguration L ℕ)}
    (hscat : BFScattered K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsatK : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) : TreeStage K 0 :=
  let h0 := exists_bfClass_subset_and_uncountable_of_saturated hscat Subset.rfl hunc hα₀ hsatK
  { level := α₀
    level_lt := hα₀
    node := fun _ => h0.choose
    subset_target := fun _ => h0.choose_spec.2.1
    uncountable_class := fun _ => h0.choose_spec.2.2 }

/-- Restrict an infinite branch `X : ℕ → Bool` to its length-`n` prefix `Fin n → Bool`. -/
private def branchPrefix (X : ℕ → Bool) (n : ℕ) : Fin n → Bool :=
  fun j => X j

/-- Taking `Fin.init` of the `(n + 1)`-prefix recovers the `n`-prefix. -/
private theorem init_branchPrefix (X : ℕ → Bool) (n : ℕ) :
    Fin.init (branchPrefix X (n + 1)) = branchPrefix X n :=
  rfl

/-- Evaluating the `(n + 1)`-prefix at `Fin.last n` reads bit `X n`. -/
private theorem branchPrefix_last (X : ℕ → Bool) (n : ℕ) :
    branchPrefix X (n + 1) (Fin.last n) = X n :=
  rfl

/-- Distinct branches `X ≠ Y` produce limit configurations that disagree at `⨆ n, (stage n).level`,
since at their first index `i` of disagreement both limits match their respective stage-`(i + 1)`
nodes, which are separated at `(stage (i + 1)).level`. -/
private theorem not_bfEquiv_of_branch_ne {K : Set (RelationalConfiguration L ℕ)}
    {stage : ∀ n, TreeStage K n}
    (hparent : ∀ n (τ : Fin (n + 1) → Bool),
      bfEquivSetoid L ℕ (stage n).level ((stage n).node (Fin.init τ)) ((stage (n + 1)).node τ))
    (hsib : ∀ n (τ₁ τ₂ : Fin (n + 1) → Bool), Fin.init τ₁ = Fin.init τ₂ →
      τ₁ (Fin.last n) ≠ τ₂ (Fin.last n) →
      ¬ bfEquivSetoid L ℕ (stage (n + 1)).level ((stage (n + 1)).node τ₁)
        ((stage (n + 1)).node τ₂))
    {limitCode : (ℕ → Bool) → RelationalConfiguration L ℕ}
    (hlimit : ∀ X i, bfEquivSetoid L ℕ (stage i).level (limitCode X)
      ((stage (i + 1)).node (branchPrefix X (i + 1))))
    {X Y : ℕ → Bool} (hXY : X ≠ Y) :
    ¬ bfEquivSetoid L ℕ (⨆ n : ℕ, (stage n).level) (limitCode X) (limitCode Y) := by
  intro heq
  have hex : ∃ n, X n ≠ Y n := Function.ne_iff.mp hXY
  let i := Nat.find hex
  have hi_ne : X i ≠ Y i := Nat.find_spec hex
  have hi_eq : branchPrefix X i = branchPrefix Y i := by
    ext ⟨j, hj⟩
    exact Classical.not_not.mp (Nat.find_min hex hj)
  have hlev : bfEquivSetoid L ℕ (stage (i + 1)).level (limitCode X) (limitCode Y) :=
    bfEquivSetoid_anti (Ordinal.le_iSup (fun n => (stage n).level) (i + 1)) heq
  have hZ (Z : ℕ → Bool) : bfEquivSetoid L ℕ (stage (i + 1)).level (limitCode Z)
      ((stage (i + 1)).node (branchPrefix Z (i + 1))) :=
    (bfEquivSetoid L ℕ (stage (i + 1)).level).trans' (hlimit Z (i + 1))
      ((bfEquivSetoid L ℕ (stage (i + 1)).level).symm'
        (by simpa only [init_branchPrefix] using hparent (i + 1) (branchPrefix Z (i + 2))))
  refine hsib i (branchPrefix X (i + 1)) (branchPrefix Y (i + 1))
    (by simpa only [init_branchPrefix] using hi_eq)
    (by simpa only [branchPrefix_last] using hi_ne) ?_
  exact (bfEquivSetoid L ℕ (stage (i + 1)).level).trans'
    ((bfEquivSetoid L ℕ (stage (i + 1)).level).symm' (hZ X))
    ((bfEquivSetoid L ℕ (stage (i + 1)).level).trans' hlev (hZ Y))

variable [Countable (Σ n, L.Relations n)]

/-- At stage `n`, if no `K ∩ modelsOf θ` is minimally uncountable, every node's level class
(which equals `K ∩ modelsOf (scottSentenceAtLevel ...)`) splits along some sentence `φ σ` into two
large sides; raising the level above `s.level + ω` and all saturation ordinals of the `2^n`
sentences `φ σ` lets us pick a large child class on each side. -/
private noncomputable def TreeStage.step {K : Set (RelationalConfiguration L ℕ)} {n : ℕ}
    (hscat : BFScattered K) (hno : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (K ∩ modelsOf θ))
    (s : TreeStage K n) : SplittingStep K s := by
  classical
  let C (σ : Fin n → Bool) := {d | bfEquivSetoid L ℕ s.level (s.node σ) d}
  -- Each `C σ` is `K ∩ modelsOf ((s.node σ).scottSentenceAtLevel s.level)`, hence not minimal.
  have hsplit (σ : Fin n → Bool) : ∃ φ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (C σ ∩ modelsOf φ)).Countable ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) '' (C σ \ modelsOf φ)).Countable := by
    refine exists_sentence_uncountable_inter_and_sdiff_of_not_minimallyUncountableOn
      (s.uncountable_class σ) fun hmin => hno ((s.node σ).scottSentenceAtLevel s.level) ?_
    rwa [modelsOf_scottSentenceAtLevel _ s.level_lt,
      inter_eq_self_of_subset_right (s.subset_target σ)]
  choose φ hφ_true hφ_false using hsplit
  choose β hβ_lt hβ_sat using fun σ =>
    exists_bfLevel_saturated_modelsOf.{_, _, _, _, 0} (V := ℕ) (φ σ)
  let α' : Ordinal.{0} := max (s.level + Ordinal.omega0) (⨆ σ : Fin n → Bool, β σ)
  have hα'_lt : α' < ω₁ := max_lt
    (Ordinal.isPrincipal_add_omega 1 s.level_lt Ordinal.omega0_lt_omega_one)
    (Ordinal.iSup_lt_omega_one hβ_lt)
  have hle_β (σ : Fin n → Bool) : β σ ≤ α' := (Ordinal.le_iSup β σ).trans (le_max_right _ _)
  let side (σ : Fin n → Bool) (b : Bool) := cond b (C σ ∩ modelsOf (φ σ)) (C σ \ modelsOf (φ σ))
  have hside_sub (σ : Fin n → Bool) (b : Bool) : side σ b ⊆ C σ := by
    cases b <;> [exact sdiff_subset; exact inter_subset_left]
  have hside_unc (σ : Fin n → Bool) (b : Bool) :
      ¬ (Quotient.mk (isoSetoid L ℕ) '' side σ b).Countable := by
    cases b <;> [exact hφ_false σ; exact hφ_true σ]
  have hside_sat (σ : Fin n → Bool) (b : Bool) (c : RelationalConfiguration L ℕ)
      (hc : c ∈ side σ b) (d : RelationalConfiguration L ℕ) (hcd : bfEquivSetoid L ℕ α' c d) :
      d ∈ side σ b := by
    have hC : d ∈ C σ := (bfEquivSetoid L ℕ s.level).trans' (hside_sub σ b hc)
      (bfEquivSetoid_anti (le_self_add.trans (le_max_left _ _)) hcd)
    have hφ := hβ_sat σ α' (hle_β σ) c d hcd
    cases b <;> [exact ⟨hC, fun hd => hc.2 (hφ.mpr hd)⟩; exact ⟨hC, hφ.mp hc.2⟩]
  have hchild (σ : Fin n → Bool) (b : Bool) :=
    exists_bfClass_subset_and_uncountable_of_saturated hscat
      ((hside_sub σ b).trans (s.subset_target σ)) (hside_unc σ b) hα'_lt (hside_sat σ b)
  let child (σ : Fin n → Bool) (b : Bool) := (hchild σ b).choose
  have hchild_mem (σ : Fin n → Bool) (b : Bool) : child σ b ∈ side σ b :=
    (hchild σ b).choose_spec.1
  refine ⟨⟨α', hα'_lt, fun τ => child (Fin.init τ) (τ (Fin.last n)),
      fun τ => ((hchild _ _).choose_spec.2.1).trans ((hside_sub _ _).trans (s.subset_target _)),
      fun τ => (hchild _ _).choose_spec.2.2⟩,
    le_max_left _ _, fun τ => hside_sub _ _ (hchild_mem _ _), fun τ₁ τ₂ hinit hlast heq => ?_⟩
  let σ := Fin.init τ₁
  have hiff : child σ (τ₁ (Fin.last n)) ∈ modelsOf (φ σ) ↔
      child σ (τ₂ (Fin.last n)) ∈ modelsOf (φ σ) :=
    hβ_sat σ α' (hle_β σ) _ _ (by simpa only [σ, hinit] using heq)
  cases hb₁ : τ₁ (Fin.last n) <;> cases hb₂ : τ₂ (Fin.last n)
  · exact hlast (hb₁.trans hb₂.symm)
  · rw [hb₁, hb₂] at hiff; exact (hchild_mem σ false).2 (hiff.mpr (hchild_mem σ true).2)
  · rw [hb₁, hb₂] at hiff; exact (hchild_mem σ false).2 (hiff.mp (hchild_mem σ true).2)
  · exact hlast (hb₁.trans hb₂.symm)

/-- **The Harnik–Makkai reduction for level-saturated scattered classes.** Let `K` be a
back-and-forth scattered set of configurations on `ℕ` in a countable relational language, meeting
uncountably many isomorphism classes and saturated at some countable back-and-forth level `α₀ < ω₁`.
Then some `L_{ω₁ω}` sentence `θ` cuts out a minimally uncountable intersection `K ∩ modelsOf θ`. -/
theorem exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered_of_saturated
    {K : Set (RelationalConfiguration L ℕ)} (hscat : BFScattered K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsatK : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (K ∩ modelsOf θ) := by
  classical
  by_contra! hno
  -- Build the splitting tree stages recursively along `ℕ`.
  let s₀ := treeStageZero hscat hunc hα₀ hsatK
  let stage : ∀ n, TreeStage K n := Nat.rec s₀ fun _ s => (s.step hscat hno).next
  have hstep (n : ℕ) := ((stage n).step hscat hno).level_step
  have hparent (n : ℕ) := ((stage n).step hscat hno).parent_equiv
  have hsib (n : ℕ) := ((stage n).step hscat hno).sibling_ne
  have hmono : Monotone fun n => (stage n).level :=
    monotone_nat_of_le_succ fun n => le_self_add.trans (hstep n)
  -- Along each branch `X : ℕ → Bool`, take the chain limit of `i ↦ (stage (i + 1)).node`.
  have hchain (X : ℕ → Bool) : ∃ d, ∀ i,
      bfEquivSetoid L ℕ (stage i).level d ((stage (i + 1)).node (branchPrefix X (i + 1))) := by
    refine exists_limit_of_bfEquiv_chain hmono fun i => bfEquivSetoid_anti (hstep i) ?_
    simpa only [init_branchPrefix] using hparent (i + 1) (branchPrefix X (i + 2))
  choose limitCode hlimit using hchain
  -- Every branch limit belongs to `K`, via stage `0`.
  have hmemK (X : ℕ → Bool) : limitCode X ∈ K :=
    (stage 0).subset_target (branchPrefix X 0) <|
      (bfEquivSetoid L ℕ (stage 0).level).trans'
        (by simpa only [init_branchPrefix] using hparent 0 (branchPrefix X 1))
        ((bfEquivSetoid L ℕ (stage 0).level).symm' (hlimit X 0))
  -- Inject Cantor space into the countable level quotient at `⨆ n, (stage n).level < ω₁`.
  let β : Ordinal.{0} := ⨆ n : ℕ, (stage n).level
  have := hscat.countable_quotient (Ordinal.iSup_lt_omega_one fun n => (stage n).level_lt)
  let f : (ℕ → Bool) → Quotient ((bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)) :=
    fun X => ⟦⟨limitCode X, hmemK X⟩⟧
  have hinj : Function.Injective f := fun X Y h => by
    by_contra hXY
    exact not_bfEquiv_of_branch_ne hparent hsib hlimit hXY
      (Quotient.exact (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)) h)
  have hunc_cantor : ¬ Countable (ℕ → Bool) := by
    rw [← mk_le_aleph0_iff]
    simpa using aleph0_lt_continuum
  exact hunc_cantor hinj.countable

/-- **The Harnik–Makkai reduction for countably branching sentences.** If the models on `ℕ` of a
sentence `Θ` with countable branching are back-and-forth scattered and meet uncountably many
isomorphism classes, some `L_{ω₁ω}` sentence `θ` cuts out a minimally uncountable intersection
`modelsOf Θ ∩ modelsOf θ`. -/
theorem exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered
    {ι : Type uι} [Countable ι] {Θ : L.SentenceInf ι}
    (hscat : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) Θ ∩ modelsOf θ) := by
  obtain ⟨α₀, hα₀, hsat⟩ := exists_bfLevel_saturated_modelsOf.{_, _, _, _, 0} (V := ℕ) Θ
  exact exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered_of_saturated hscat hunc hα₀
    fun c hc d hcd => (hsat α₀ le_rfl c d hcd).mp hc

/-- **The Harnik–Makkai reduction.** In a countable relational language, every `L_{ω₁ω}` sentence
`Θ` whose models on `ℕ` are back-and-forth scattered and meet uncountably many isomorphism classes
has a minimally uncountable strengthening `Θ ⊓ θ`. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered {Θ : L.Sentenceω}
    (hscat : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  simpa only [modelsOf_inf] using
    exists_minimallyUncountableOn_inter_modelsOf_of_bfScattered hscat hunc

/-- **Rank form of the Harnik–Makkai reduction.** For any isolating rank `ρ`, if the models on `ℕ`
of `Θ` are back-and-forth scattered and `ρ` is unbounded below `ω₁` on them, some strengthening
`Θ ⊓ θ` is minimally unbounded for `ρ`. -/
theorem exists_minimallyUnboundedOn_inf_of_bfScattered
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ) {Θ : L.Sentenceω}
    (hscat : BFScattered (modelsOf (V := ℕ) Θ))
    (hunb : UnboundedRankOn ρ (modelsOf (V := ℕ) Θ)) :
    ∃ θ : L.Sentenceω, MinimallyUnboundedOn ρ (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  have hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable := fun hc =>
    unboundedRankOn_iff_not_boundedRankOn.1 hunb
      ((hρ.countable_image_isoSetoid_iff_boundedRankOn hscat).mp hc)
  obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc
  have hscat' : BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) :=
    hscat.mono (modelsOf_inf Θ θ ▸ inter_subset_left)
  exact ⟨θ, (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hscat').mp hmin⟩

/-- **Reducing a Vaught counterexample to a minimally uncountable one.** If `Θ` fails
`HasVaughtDichotomy`, some strengthening `Θ ⊓ ψ` also fails `HasVaughtDichotomy` and has
back-and-forth scattered, minimally uncountable models on `ℕ`. -/
theorem exists_bfScattered_and_minimallyUncountableOn_of_not_hasVaughtDichotomy
    {Θ : L.Sentenceω} (hΘ : ¬ HasVaughtDichotomy Θ) :
    ∃ ψ : L.Sentenceω, ¬ HasVaughtDichotomy (Θ ⊓ ψ) ∧
      BFScattered (modelsOf (V := ℕ) (Θ ⊓ ψ)) ∧
      MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ ψ)) := by
  have hnat : ¬ (Countable (Quotient (isoSetoidOn ℕ Θ)) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOf Θ)) :=
    fun h => hΘ (hasVaughtDichotomy_of_nat h)
  rw [not_or] at hnat
  have hscat : BFScattered (modelsOf (V := ℕ) Θ) :=
    (isThinOnNatModels_iff.2 hnat.2).bfScattered_modelsOf
  have hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable :=
    fun hc => hnat.1 (Setoid.countable_quotient_comap_val_iff.2 hc)
  obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc
  have hscat' : BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) :=
    hscat.mono (modelsOf_inf Θ θ ▸ inter_subset_left)
  -- Conjoining `infiniteSentence` kills all finite models without changing the models on `ℕ`.
  refine ⟨θ ⊓ L.infiniteSentence, fun hdich => ?_, hscat.mono (by simp [modelsOf_inf]), ?_⟩
  · have hdich' : HasVaughtDichotomy (Θ ⊓ θ ⊓ L.infiniteSentence) :=
      hasVaughtDichotomy_iff.2 <| (hasVaughtDichotomy_iff.1 hdich).imp
        (fun hle => (countableModelCount_le_of_subset
          (by simp [modelsOf_inf])
          (fun _ => by simp [modelsOf_inf])).trans hle)
        (fun hperf => by
          simpa only [hasPerfectlyManyCountableModels_iff, modelsOf_inf, inter_assoc] using hperf)
    rcases (hasVaughtDichotomy_inf_infiniteSentence_iff (Θ ⊓ θ)).1 hdich' with hc | hperf
    · exact hmin.1 (Setoid.countable_quotient_comap_val_iff.1 hc)
    · exact (Setoid.isThinOn_iff.1 hscat'.isThinOn) hperf
  · simpa only [modelsOf_inf, modelsOf_infiniteSentence_of_infinite, inter_univ,
      inter_assoc] using hmin

end SplittingTree

/-! ### Minimal-counterexample formulations of Vaught's conjecture -/

section VaughtEquivalences

/-- Any `L_{ω₁ω}` sentence in `Language.{0, 0}` with back-and-forth scattered, minimally uncountable
models on `ℕ` refutes `VaughtConjecture`. -/
theorem not_vaughtConjecture_of_bfScattered_of_minimallyUncountableOn
    {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω}
    (hscat : BFScattered (modelsOf (V := ℕ) φ))
    (hmin : MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    ¬ VaughtConjecture := fun hv =>
  hmin.1 (Setoid.countable_quotient_comap_val_iff.1
    ((vaughtConjecture_iff_bfScattered.1 hv) L φ hscat))

/-- **Minimal-counterexample formulation of Vaught's conjecture (Harnik–Makkai; Steel).** Vaught's
perfect-set conjecture holds if and only if no `L_{ω₁ω}` sentence with back-and-forth scattered
models on `ℕ` has minimally uncountable models on `ℕ`. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      BFScattered (modelsOf (V := ℕ) φ) → ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) := by
  constructor
  · intro hv L _ _ φ hscat hmin
    exact not_vaughtConjecture_of_bfScattered_of_minimallyUncountableOn hscat hmin hv
  · intro h
    refine vaughtConjecture_iff_bfScattered.2 fun L _ _ φ hscat => ?_
    by_contra hunc
    have hunc' : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) φ).Countable :=
      fun hc => hunc (Setoid.countable_quotient_comap_val_iff.2 hc)
    obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc'
    exact h L (φ ⊓ θ) (hscat.mono (modelsOf_inf φ θ ▸ inter_subset_left)) hmin

/-- **Minimally unbounded formulation of Vaught's conjecture (Montalbán, Theorem XII.7).** Vaught's
conjecture holds if and only if, for every isolating rank `ρ`, no `L_{ω₁ω}` sentence with
back-and-forth scattered models on `ℕ` is minimally unbounded for `ρ` on `ℕ`. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω)
      (ρ : RelationalConfiguration L ℕ → Ordinal.{0}), IsIsolatingRank ρ →
      BFScattered (modelsOf (V := ℕ) φ) → ¬ MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ) := by
  rw [vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn]
  constructor
  · intro h L _ _ φ ρ hρ hscat hmin
    exact h L φ hscat ((hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hscat).2 hmin)
  · intro h L _ _ φ hscat hmin
    exact h L φ _ (isIsolatingRank_scottHeight L) hscat
      (((isIsolatingRank_scottHeight L).minimallyUncountableOn_iff_minimallyUnboundedOn hscat).1
        hmin)

/-- **Concentration formulation of Vaught's conjecture.** Vaught's conjecture holds if and only if
every `L_{ω₁ω}` sentence whose models on `ℕ` are concentrated at back-and-forth levels has countably
many models on `ℕ` up to isomorphism. -/
theorem vaughtConjecture_iff_forall_concentratedAtBFLevels_countable :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) → Countable (Quotient (isoSetoidOn ℕ φ)) := by
  constructor
  · intro hv L _ _ φ hconc
    exact (vaughtConjecture_iff_bfScattered.1 hv) L φ hconc.bfScattered
  · intro h
    refine vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn.2
      fun L _ _ φ hscat hmin => ?_
    exact hmin.1 (Setoid.countable_quotient_comap_val_iff.1
      (h L φ (hmin.concentratedAtBFLevels_of_bfScattered hscat)))

end VaughtEquivalences

end TauCeti
