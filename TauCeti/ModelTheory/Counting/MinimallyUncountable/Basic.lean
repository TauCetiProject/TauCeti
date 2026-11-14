/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Thin

/-!
# Minimally uncountable and minimally unbounded classes of models

A class `K` of relational configurations on a carrier `V` is **minimally uncountable**
(`TauCeti.MinimallyUncountableOn K`) when it meets uncountably many isomorphism classes, yet every
cut by an `L_{ω₁ω}` sentence `θ` leaves either `K ∩ modelsOf θ` or `K \ modelsOf θ` meeting only
countably many isomorphism classes. Analogously, for an ordinal-valued rank `ρ`, `K` is **minimally
unbounded** (`TauCeti.MinimallyUnboundedOn ρ K`) when `ρ` is unbounded below `ω₁` on `K` and every
sentence cut has a side on which `ρ` is bounded below `ω₁`.

Both properties pass to any subset that remains uncountable up to isomorphism (or rank-unbounded).
In a countable relational vocabulary on a countable carrier, whenever `K` meets only countably many
classes at a countable back-and-forth level `α < ω₁`, one `α`-class meets `K` in a subset that is
again minimally uncountable (respectively minimally unbounded) while its complement in `K` is
countable up to isomorphism (respectively rank-bounded).

On the carrier `ℕ`, when `K` is back-and-forth scattered (`TauCeti.BFScattered K`):

* For every isolating rank `ρ`, `MinimallyUncountableOn K` is equivalent to
  `MinimallyUnboundedOn ρ K`, with no countability hypothesis on the language and no definability or
  invariance assumption on `K`. In particular, minimal unboundedness on a scattered class does not
  depend on which isolating rank is chosen, and `K` meets `ℵ₁` isomorphism classes.
* In a countable relational vocabulary, a scattered minimally uncountable class is concentrated at
  back-and-forth levels (`TauCeti.ConcentratedAtBFLevels K`). Conversely, an analytic concentrated
  class meeting uncountably many isomorphism classes is both scattered and minimally uncountable.
  Hence for any `L_{ω₁ω}` sentence `φ`, `modelsOf (V := ℕ) φ` is scattered (equivalently, `φ` is
  thin on `ℕ`) and minimally uncountable if and only if it is concentrated at back-and-forth levels
  and `φ` has uncountably many models on `ℕ` up to isomorphism.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes and every
  `L_{ω₁ω}` sentence cut of `K` has a countable side up to isomorphism.
* `TauCeti.MinimallyUnboundedOn ρ K`: `ρ` is unbounded below `ω₁` on `K` and every `L_{ω₁ω}`
  sentence cut of `K` has a side on which `ρ` is bounded below `ω₁`.

## Main results

* `TauCeti.MinimallyUncountableOn.of_subset` and `TauCeti.MinimallyUnboundedOn.of_subset`:
  hereditary closure on large subsets.
* `TauCeti.MinimallyUncountableOn.exists_bfClass` and
  `TauCeti.MinimallyUnboundedOn.exists_bfClass`: at any countable level with countably many classes
  on `K`, one level class intersects `K` in a minimally uncountable (or minimally unbounded) set
  with small complement.
* `TauCeti.IsIsolatingRank.minimallyUncountableOn_iff_minimallyUnboundedOn` and
  `TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`: equivalence of minimal uncountability and
  minimal unboundedness on scattered classes, and invariance across isolating ranks.
* `TauCeti.bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels_of_analyticSet`,
  `TauCeti.bfScattered_and_minimallyUncountableOn_modelsOf_iff`,
  `TauCeti.isThinOnNatModels_and_minimallyUncountableOn_modelsOf_iff`, and
  `TauCeti.IsIsolatingRank.bfScattered_and_minimallyUnboundedOn_modelsOf_iff`: concentration and
  isolating-rank characterizations on analytic classes and `L_{ω₁ω}` model classes.

## References

* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proceedings of
  the American Mathematical Society 67 (1977), 309–314.
* John R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689,
  Springer, 1978, 193–208.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII, §XII.2 (minimally unbounded sentences and concentration).
* `MinimallyUncountableOn` and the concentration characterization of scattered minimally uncountable
  sentences follow `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`, Apache-2.0),
  generalized here to arbitrary carriers, arbitrary languages, and isolating ranks via
  `MinimallyUnboundedOn`.
-/

public section

universe u v w o r

open Cardinal FirstOrder FirstOrder.Language MeasureTheory Ordinal Set

namespace TauCeti

open RelationalConfiguration

section GeneralCarrier

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}
variable {A K : Set (RelationalConfiguration L V)} {ρ : RelationalConfiguration L V → Ordinal.{r}}

/-! ### Minimally uncountable classes -/

/-- A set `K` of configurations on `V` is **minimally uncountable** when it meets uncountably many
isomorphism classes, and every cut by an `L_{ω₁ω}` sentence leaves one side meeting at most
countably many isomorphism classes. -/
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

/-- Reformulation of `TauCeti.MinimallyUncountableOn` through restricted isomorphism quotients. -/
theorem minimallyUncountableOn_iff_countable_quotient :
    MinimallyUncountableOn K ↔
      ¬ Countable (Quotient ((isoSetoid L V).comap (Subtype.val : K → _))) ∧
        ∀ θ : L.Sentenceω,
          Countable (Quotient ((isoSetoid L V).comap (Subtype.val : ↥(K ∩ modelsOf θ) → _))) ∨
            Countable (Quotient ((isoSetoid L V).comap (Subtype.val : ↥(K \ modelsOf θ) → _))) := by
  simp only [minimallyUncountableOn_iff, Setoid.countable_quotient_comap_val_iff]

/-- A minimally uncountable set meets uncountably many isomorphism classes. -/
theorem MinimallyUncountableOn.not_countable_image (h : MinimallyUncountableOn K) :
    ¬ (Quotient.mk (isoSetoid L V) '' K).Countable :=
  h.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally uncountable set has a side meeting countably many
isomorphism classes. -/
theorem MinimallyUncountableOn.countable_image_inter_or_sdiff (h : MinimallyUncountableOn K)
    (θ : L.Sentenceω) :
    (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  h.2 θ

/-- Restricted isomorphism on a minimally uncountable set has uncountably many classes. -/
theorem MinimallyUncountableOn.not_countable_quotient (h : MinimallyUncountableOn K) :
    ¬ Countable (Quotient ((isoSetoid L V).comap (Subtype.val : K → _))) :=
  Setoid.countable_quotient_comap_val_iff.not.mpr h.1

/-- `Uncountable` form of `TauCeti.MinimallyUncountableOn.not_countable_quotient`. -/
theorem MinimallyUncountableOn.uncountable_quotient (h : MinimallyUncountableOn K) :
    Uncountable (Quotient ((isoSetoid L V).comap (Subtype.val : K → _))) :=
  not_countable_iff.mp h.not_countable_quotient

/-- A minimally uncountable set is nonempty. -/
theorem MinimallyUncountableOn.nonempty (h : MinimallyUncountableOn K) : K.Nonempty :=
  nonempty_iff_ne_empty.mpr fun h0 => h.1 (by simp [h0])

/-- The empty set is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L V)) :=
  fun h => not_nonempty_empty h.nonempty

/-- Any subset of a minimally uncountable set that still meets uncountably many isomorphism classes
is itself minimally uncountable. -/
theorem MinimallyUncountableOn.of_subset (hK : MinimallyUncountableOn K) (hAK : A ⊆ K)
    (hA : ¬ (Quotient.mk (isoSetoid L V) '' A).Countable) : MinimallyUncountableOn A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (image_mono (inter_subset_inter_left _ hAK)))
    (fun h => h.mono (image_mono (sdiff_le_sdiff_right hAK)))⟩

/-- For the model class of a sentence `φ : L.Sentenceω` on `V`, minimal uncountability means that
`φ` has uncountably many models on `V` up to isomorphism while for every `θ : L.Sentenceω` either
`φ ⊓ θ` or `φ ⊓ θ.not` has countably many. -/
theorem minimallyUncountableOn_modelsOf_iff_quotient (φ : L.Sentenceω) :
    MinimallyUncountableOn (modelsOf (V := V) φ) ↔
      ¬ Countable (Quotient (isoSetoidOn V φ)) ∧
        ∀ θ : L.Sentenceω,
          Countable (Quotient (isoSetoidOn V (φ ⊓ θ))) ∨
            Countable (Quotient (isoSetoidOn V (φ ⊓ θ.not))) := by
  simp only [minimallyUncountableOn_iff, isoSetoidOn, Setoid.countable_quotient_comap_val_iff,
    modelsOf_inf, modelsOf_not, ← sdiff_eq]

/-! ### Minimally unbounded classes -/

/-- A set `K` of configurations on `V` is **minimally unbounded** for an ordinal-valued rank `ρ`
when `ρ` is unbounded below `ω₁` on `K` and every cut by an `L_{ω₁ω}` sentence has a side on which
`ρ` is bounded below `ω₁`. -/
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

/-- The rank `ρ` is unbounded below `ω₁` on a minimally unbounded set. -/
theorem MinimallyUnboundedOn.unboundedRankOn (h : MinimallyUnboundedOn ρ K) : UnboundedRankOn ρ K :=
  h.1

/-- Every `L_{ω₁ω}` sentence cut of a minimally unbounded set has a rank-bounded side. -/
theorem MinimallyUnboundedOn.boundedRankOn_inter_or_sdiff (h : MinimallyUnboundedOn ρ K)
    (θ : L.Sentenceω) :
    BoundedRankOn ρ (K ∩ modelsOf θ) ∨ BoundedRankOn ρ (K \ modelsOf θ) :=
  h.2 θ

/-- A minimally unbounded set is nonempty. -/
theorem MinimallyUnboundedOn.nonempty (h : MinimallyUnboundedOn ρ K) : K.Nonempty :=
  nonempty_iff_ne_empty.mpr fun h0 => not_unboundedRankOn_empty ρ (h0 ▸ h.1)

/-- No rank is minimally unbounded on the empty set. -/
@[simp]
theorem not_minimallyUnboundedOn_empty :
    ¬ MinimallyUnboundedOn ρ (∅ : Set (RelationalConfiguration L V)) :=
  fun h => not_nonempty_empty h.nonempty

/-- Any rank-unbounded subset of a minimally unbounded set is again minimally unbounded. -/
theorem MinimallyUnboundedOn.of_subset (hK : MinimallyUnboundedOn ρ K) (hAK : A ⊆ K)
    (hA : UnboundedRankOn ρ A) : MinimallyUnboundedOn ρ A :=
  ⟨hA, fun θ => (hK.2 θ).imp
    (fun h => h.mono (inter_subset_inter_left _ hAK))
    (fun h => h.mono (sdiff_le_sdiff_right hAK))⟩

/-- Sentence-conjunction form of `TauCeti.MinimallyUnboundedOn` on `modelsOf φ`. -/
theorem minimallyUnboundedOn_modelsOf_iff (φ : L.Sentenceω) :
    MinimallyUnboundedOn ρ (modelsOf (V := V) φ) ↔
      UnboundedRankOn ρ (modelsOf (V := V) φ) ∧
        ∀ θ : L.Sentenceω,
          BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ)) ∨
            BoundedRankOn ρ (modelsOf (V := V) (φ ⊓ θ.not)) := by
  simp only [minimallyUnboundedOn_iff, modelsOf_inf, modelsOf_not, ← sdiff_eq]

/-! ### Selecting a large back-and-forth class -/

/-- If a minimally uncountable class `K` on a countable carrier meets countably many classes at
level `α < ω₁`, then one level-`α` class intersects `K` in a minimally uncountable set whose
complement in `K` meets only countably many isomorphism classes. -/
theorem MinimallyUncountableOn.exists_bfClass [∀ n, Countable (L.Relations n)] [Countable V]
    (hK : MinimallyUncountableOn K) {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      MinimallyUncountableOn (K ∩ {d | bfEquivSetoid L V α c d}) ∧
        (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable := by
  obtain ⟨c, hcK, hunc, hcount⟩ :=
    exists_bfClass_uncountable_isoClasses_and_countable_sdiff hK.1 hK.2 hα
  exact ⟨c, hcK, hK.of_subset inter_subset_left hunc, hcount⟩

/-- If a minimally unbounded class `K` on a countable carrier meets countably many classes at
level `α < ω₁`, then one level-`α` class intersects `K` in a minimally unbounded set whose
complement in `K` has rank bounded below `ω₁`. -/
theorem MinimallyUnboundedOn.exists_bfClass [∀ n, Countable (L.Relations n)] [Countable V]
    (hK : MinimallyUnboundedOn ρ K) {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      MinimallyUnboundedOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∧
        BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) := by
  obtain ⟨c, hcK, hunb, hbnd⟩ :=
    exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff hK.1 hK.2 hα
  exact ⟨c, hcK, hK.of_subset inter_subset_left hunb, hbnd⟩

end GeneralCarrier

/-! ### Scattered classes, isolating ranks, and concentration on `ℕ` -/

section NatCarrier

variable {L : Language.{u, v}} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}
variable {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}}

/-- Image-countability form of `TauCeti.IsIsolatingRank.countable_isoClasses_iff_bounded` via
`TauCeti.BoundedRankOn`. -/
theorem IsIsolatingRank.countable_image_iff_boundedRankOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    (Quotient.mk (isoSetoid L ℕ) '' K).Countable ↔ BoundedRankOn ρ K := by
  rw [← Setoid.countable_quotient_comap_val_iff, hρ.countable_isoClasses_iff_bounded hK,
    boundedRankOn_iff]

/-- Contrapositive form of `TauCeti.IsIsolatingRank.countable_image_iff_boundedRankOn`: a scattered
set meets uncountably many isomorphism classes precisely when any isolating rank is unbounded below
`ω₁` on it. -/
theorem IsIsolatingRank.not_countable_image_iff_unboundedRankOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ↔ UnboundedRankOn ρ K := by
  rw [hρ.countable_image_iff_boundedRankOn hK, unboundedRankOn_iff_not_boundedRankOn]

/-- **Minimal uncountability equals minimal unboundedness on scattered classes.** For any isolating
rank `ρ` and any back-and-forth scattered set `K` of configurations on `ℕ`, `K` is minimally
uncountable if and only if `K` is minimally unbounded for `ρ`. No countability hypothesis on `L` and
no definability or invariance of `K` is assumed. -/
theorem IsIsolatingRank.minimallyUncountableOn_iff_minimallyUnboundedOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    MinimallyUncountableOn K ↔ MinimallyUnboundedOn ρ K := by
  rw [minimallyUncountableOn_iff, minimallyUnboundedOn_iff,
    hρ.not_countable_image_iff_unboundedRankOn hK]
  refine and_congr_right' (forall_congr' fun θ => ?_)
  rw [hρ.countable_image_iff_boundedRankOn (hK.mono inter_subset_left),
    hρ.countable_image_iff_boundedRankOn (hK.mono sdiff_subset)]

/-- On a back-and-forth scattered set, minimal unboundedness is independent of the choice of
isolating rank. -/
theorem IsIsolatingRank.minimallyUnboundedOn_iff (hρ : IsIsolatingRank ρ) (hσ : IsIsolatingRank σ)
    (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn σ K :=
  (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hK).symm.trans
    (hσ.minimallyUncountableOn_iff_minimallyUnboundedOn hK)

/-- A back-and-forth scattered minimally uncountable set meets `ℵ₁` isomorphism classes. -/
theorem BFScattered.mk_isoClasses_eq_aleph_one_of_minimallyUncountableOn (hK : BFScattered K)
    (hmin : MinimallyUncountableOn K) :
    #(Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) = ℵ₁ := by
  have := hmin.uncountable_quotient
  exact (isIsolatingRank_scottHeight L).mk_isoClasses_eq_aleph_one hK

/-- In a countable relational vocabulary, a back-and-forth scattered minimally uncountable class is
concentrated at back-and-forth levels. No definability or invariance of `K` is needed. -/
theorem BFScattered.concentratedAtBFLevels_of_minimallyUncountableOn
    [∀ n, Countable (L.Relations n)] (hK : BFScattered K) (hmin : MinimallyUncountableOn K) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK hmin.2

/-- In a countable relational vocabulary, an analytic concentrated class meeting uncountably many
isomorphism classes is minimally uncountable. The class itself need not be isomorphism invariant. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn_of_analyticSet
    [∀ n, Countable (L.Relations n)] (hK : ConcentratedAtBFLevels K) (hKan : AnalyticSet K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    MinimallyUncountableOn K := by
  refine ⟨hunc, fun θ => ?_⟩
  simpa only [Setoid.countable_quotient_comap_val_iff] using
    hK.countable_isoClasses_inter_modelsOf_or_sdiff hKan θ

/-- **Concentration characterization on analytic classes.** In a countable relational vocabulary, an
analytic set `K` of configurations on `ℕ` is back-and-forth scattered and minimally uncountable if
and only if it is concentrated at back-and-forth levels and meets uncountably many isomorphism
classes. -/
theorem bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels_of_analyticSet
    [∀ n, Countable (L.Relations n)] (hKan : AnalyticSet K) :
    BFScattered K ∧ MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun ⟨hscat, hmin⟩ => ⟨hscat.concentratedAtBFLevels_of_minimallyUncountableOn hmin, hmin.1⟩,
    fun ⟨hconc, hunc⟩ => ⟨hconc.bfScattered, hconc.minimallyUncountableOn_of_analyticSet hKan hunc⟩⟩

/-- **Concentration characterization of scattered minimally uncountable sentences.** In a countable
relational vocabulary, the model class on `ℕ` of an `L_{ω₁ω}` sentence `φ` is back-and-forth
scattered and minimally uncountable if and only if it is concentrated at back-and-forth levels and
`φ` has uncountably many models on `ℕ` up to isomorphism. -/
theorem bfScattered_and_minimallyUncountableOn_modelsOf_iff [∀ n, Countable (L.Relations n)]
    (φ : L.Sentenceω) :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels_of_analyticSet
      (measurableSet_modelsOf φ).analyticSet,
    isoSetoidOn, Setoid.countable_quotient_comap_val_iff]

/-- Thin-sentence form of `TauCeti.bfScattered_and_minimallyUncountableOn_modelsOf_iff`. -/
theorem isThinOnNatModels_and_minimallyUncountableOn_modelsOf_iff [∀ n, Countable (L.Relations n)]
    (φ : L.Sentenceω) :
    IsThinOnNatModels φ ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [← bfScattered_modelsOf_iff_isThinOnNatModels,
    bfScattered_and_minimallyUncountableOn_modelsOf_iff]

/-- Isolating-rank form of `TauCeti.bfScattered_and_minimallyUncountableOn_modelsOf_iff`: for any
isolating rank `ρ`, the models on `ℕ` of `φ` are scattered and minimally unbounded for `ρ` if and
only if they are concentrated at back-and-forth levels and `ρ` is unbounded below `ω₁` on them. -/
theorem IsIsolatingRank.bfScattered_and_minimallyUnboundedOn_modelsOf_iff
    [∀ n, Countable (L.Relations n)] (hρ : IsIsolatingRank ρ) (φ : L.Sentenceω) :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧ UnboundedRankOn ρ (modelsOf (V := ℕ) φ) := by
  constructor
  · rintro ⟨hscat, hmin⟩
    have hmin' := (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hscat).2 hmin
    exact ⟨hscat.concentratedAtBFLevels_of_minimallyUncountableOn hmin', hmin.1⟩
  · rintro ⟨hconc, hunb⟩
    have hscat := hconc.bfScattered
    have hunc := (hρ.not_countable_image_iff_unboundedRankOn hscat).2 hunb
    exact ⟨hscat, (hρ.minimallyUncountableOn_iff_minimallyUnboundedOn hscat).1
      (hconc.minimallyUncountableOn_of_analyticSet (measurableSet_modelsOf φ).analyticSet hunc)⟩

end NatCarrier

end TauCeti
