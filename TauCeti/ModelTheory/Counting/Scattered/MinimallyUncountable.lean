/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.MinimallyUncountable
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Vaught
public import TauCeti.ModelTheory.RelationalConfiguration.Saturation

/-!
# Scattered minimally uncountable classes and the Harnik–Makkai reduction

This file connects `TauCeti.MinimallyUncountableOn` and `TauCeti.MinimallyUnboundedOn` to
back-and-forth scatteredness, concentration at back-and-forth levels, isolating ranks, and
Vaught's conjecture, and proves the Harnik–Makkai reduction of scattered counterexamples to
minimally uncountable strengthenings.

On the classification side:
* Any class on `ℕ` that is concentrated at back-and-forth levels and meets uncountably many
  isomorphism classes is minimally uncountable
  (`TauCeti.ConcentratedAtBFLevels.minimallyUncountableOn`): every `L_{ω₁ω}` sentence is saturated
  from some countable back-and-forth level onward, where concentration makes one side of the cut
  countable. No definability or isomorphism invariance of the class is needed.
* Conversely, any back-and-forth scattered class whose sentence cuts each have a countable side is
  concentrated (`TauCeti.BFScattered.concentratedAtBFLevels_of_minimallyUncountableOn`). Thus a set
  of configurations on `ℕ` is both back-and-forth scattered and minimally uncountable if and only if
  it is concentrated at back-and-forth levels and meets uncountably many isomorphism classes.
* On any back-and-forth scattered class `K`, an isolating rank `ρ` is bounded below `ω₁` on a
  subset of `K` precisely when that subset meets countably many isomorphism classes. Hence
  `MinimallyUnboundedOn ρ K` is equivalent to `MinimallyUncountableOn K`, and is independent of the
  choice of isolating rank (`TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`).

On the reduction side (`TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`), if the models
on `ℕ` of `Θ : L.Sentenceω` are back-and-forth scattered and meet uncountably many isomorphism
classes, then some strengthening `Θ ⊓ θ` is minimally uncountable on `ℕ`. Otherwise a binary
splitting tree of large back-and-forth classes inside `modelsOf Θ`, along countable levels growing
by at least `ω` at each step and above the saturation levels of the splitting sentences, yields via
`TauCeti.RelationalConfiguration.exists_limit_of_bfEquiv_chain` continuum many limit models in
`modelsOf Θ` pairwise inequivalent at a single countable supremum level, contradicting
scatteredness. Combining this reduction with `TauCeti.vaughtConjecture_iff_bfScattered` shows that
Vaught's conjecture holds if and only if no back-and-forth scattered (or thin) sentence has
minimally uncountable models on `ℕ`.

## Main results

* `TauCeti.ConcentratedAtBFLevels.minimallyUncountableOn` and
  `TauCeti.ConcentratedAtBFLevels.minimallyUncountableOn_modelsOf`: concentrated classes on `ℕ`
  with uncountably many isomorphism classes are minimally uncountable.
* `TauCeti.BFScattered.minimallyUncountableOn_iff_concentratedAtBFLevels`,
  `TauCeti.bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels`, and
  `TauCeti.IsThinOnNatModels.minimallyUncountableOn_modelsOf_iff`: scattered and thin
  characterizations via concentration.
* `TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff_minimallyUncountableOn` and
  `TauCeti.IsIsolatingRank.minimallyUnboundedOn_iff`: on scattered classes, minimal unboundedness
  agrees with minimal uncountability and is independent of the isolating rank.
* `TauCeti.BFScattered.exists_bfEquivSetoid_subset_not_countable_isoClasses`: a scattered class
  saturated at a countable level `α` and meeting uncountably many isomorphism classes contains an
  entire level-`α` class meeting uncountably many isomorphism classes.
* `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered` and
  `TauCeti.exists_minimallyUnboundedOn_inf_of_bfScattered`: the Harnik–Makkai reduction to a
  minimally uncountable (or minimally unbounded) strengthening.
* `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn`,
  `TauCeti.vaughtConjecture_iff_forall_isThinOnNatModels_not_minimallyUncountableOn`, and
  `TauCeti.vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn`: minimal-counterexample
  formulations of Vaught's conjecture.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proc. Amer. Math. Soc. 67
  (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII, §XII.2
  (Definition XII.4 and Theorem XII.7, minimal counterexamples via a back-and-forth splitting tree).
* The concentration and isolating-rank characterizations of minimally uncountable and minimally
  unbounded classes follow `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` and
  `InfinitaryLogic/Descriptive/MinimallyUnbounded.lean` in Cameron Freer's
  `cameronfreer/infinitary-logic` at checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`
  (Apache-2.0); here no definability of the ambient class is needed in the concentration
  characterization, and the Harnik–Makkai splitting tree, reduction theorem, and Vaught-conjecture
  equivalences are new.
-/

public section

universe u v w o r uι

open FirstOrder FirstOrder.Language Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

section LevelSelection

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]
variable {V : Type w} [Countable V]

/-- On a minimally uncountable class meeting countably many classes at level `α < ω₁`, one
level-`α` class meets uncountably many isomorphism classes and its complement meets countably
many. -/
theorem MinimallyUncountableOn.exists_bfClass_uncountable_isoClasses_and_countable_sdiff
    {K : Set (RelationalConfiguration L V)} (hK : MinimallyUncountableOn K)
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K,
      ¬ (Quotient.mk (isoSetoid L V) '' (K ∩ {d | bfEquivSetoid L V α c d})).Countable ∧
        (Quotient.mk (isoSetoid L V) '' (K \ {d | bfEquivSetoid L V α c d})).Countable :=
  TauCeti.exists_bfClass_uncountable_isoClasses_and_countable_sdiff
    hK.not_countable_isoClasses hK.countable_inter_or_sdiff hα

/-- On a minimally unbounded class meeting countably many classes at level `α < ω₁`, one level-`α`
class is rank-unbounded and its complement is rank-bounded. -/
theorem MinimallyUnboundedOn.exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff
    {ρ : RelationalConfiguration L V → Ordinal.{r}}
    {K : Set (RelationalConfiguration L V)} (hK : MinimallyUnboundedOn ρ K)
    {α : Ordinal.{o}} (hα : α < ω₁)
    [Countable (Quotient ((bfEquivSetoid L V α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, UnboundedRankOn ρ (K ∩ {d | bfEquivSetoid L V α c d}) ∧
      BoundedRankOn ρ (K \ {d | bfEquivSetoid L V α c d}) :=
  TauCeti.exists_bfClass_unboundedRankOn_and_boundedRankOn_sdiff
    hK.unboundedRankOn hK.boundedRankOn_inter_or_sdiff hα

end LevelSelection

section ConcentrationAndRanks

variable {L : Language.{u, v}} [L.IsRelational]

/-- Any concentrated class of configurations on `ℕ` meeting uncountably many isomorphism classes is
minimally uncountable. Neither definability nor isomorphism invariance of `C` is required. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn [∀ n, Countable (L.Relations n)]
    {C : Set (RelationalConfiguration L ℕ)} (hC : ConcentratedAtBFLevels C)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' C).Countable) :
    MinimallyUncountableOn C := by
  refine minimallyUncountableOn_iff.2 ⟨hunc, fun θ => ?_⟩
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) θ
  have h := hC.countable_isoClasses_or_of_saturated
    (inter_subset_left : C ∩ modelsOf θ ⊆ C) hα
    fun b hb c hc hbc => ⟨hc, (hsat α le_rfl b c hbc).mp hb.2⟩
  have hdiff : C \ (C ∩ modelsOf θ) = C \ modelsOf θ := by ext; simp
  simp only [Setoid.countable_quotient_comap_val_iff] at h
  rwa [hdiff] at h

/-- If the models on `ℕ` of a sentence `φ` are concentrated and form uncountably many isomorphism
classes, then `modelsOf φ` is minimally uncountable. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn_modelsOf [∀ n, Countable (L.Relations n)]
    {ι : Type uι} {φ : L.SentenceInf ι}
    (hφ : ConcentratedAtBFLevels (modelsOf (V := ℕ) φ))
    (hunc : ¬ Countable (Quotient (isoSetoidOn ℕ φ))) :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) :=
  hφ.minimallyUncountableOn fun hc => hunc (Setoid.countable_quotient_comap_val_iff.2 hc)

/-- A back-and-forth scattered minimally uncountable class on `ℕ` is concentrated at back-and-forth
levels. -/
theorem BFScattered.concentratedAtBFLevels_of_minimallyUncountableOn
    [Countable (Σ n, L.Relations n)] {K : Set (RelationalConfiguration L ℕ)}
    (hK : BFScattered K) (hmin : MinimallyUncountableOn K) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK hmin.countable_inter_or_sdiff

/-- A back-and-forth scattered class on `ℕ` is minimally uncountable if and only if it is
concentrated at back-and-forth levels and meets uncountably many isomorphism classes. No
definability or isomorphism invariance of `K` is needed. -/
theorem BFScattered.minimallyUncountableOn_iff_concentratedAtBFLevels
    [Countable (Σ n, L.Relations n)] {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun hmin => ⟨hK.concentratedAtBFLevels_of_minimallyUncountableOn hmin,
      hmin.not_countable_isoClasses⟩,
    fun ⟨hconc, hunc⟩ => hconc.minimallyUncountableOn hunc⟩

/-- A set of configurations on `ℕ` is both back-and-forth scattered and minimally uncountable if
and only if it is concentrated at back-and-forth levels and meets uncountably many isomorphism
classes. -/
theorem bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels
    [Countable (Σ n, L.Relations n)] {K : Set (RelationalConfiguration L ℕ)} :
    BFScattered K ∧ MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun ⟨hscat, hmin⟩ => (hscat.minimallyUncountableOn_iff_concentratedAtBFLevels).1 hmin,
    fun ⟨hconc, hunc⟩ => ⟨hconc.bfScattered, hconc.minimallyUncountableOn hunc⟩⟩

/-- For any sentence `φ`, `modelsOf φ` on `ℕ` is both back-and-forth scattered and minimally
uncountable if and only if it is concentrated at back-and-forth levels and has uncountably many
isomorphism classes. -/
theorem bfScattered_and_minimallyUncountableOn_modelsOf_iff
    [Countable (Σ n, L.Relations n)] {ι : Type uι} {φ : L.SentenceInf ι} :
    BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧
        ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [bfScattered_and_minimallyUncountableOn_iff_concentratedAtBFLevels, isoSetoidOn,
    Setoid.countable_quotient_comap_val_iff]

/-- For a thin sentence `φ` with countable branching, `modelsOf φ` on `ℕ` is minimally uncountable
if and only if it is concentrated at back-and-forth levels and has uncountably many isomorphism
classes. -/
theorem IsThinOnNatModels.minimallyUncountableOn_modelsOf_iff
    [Countable (Σ n, L.Relations n)] {ι : Type uι} [Countable ι] {φ : L.SentenceInf ι}
    (hthin : IsThinOnNatModels φ) :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ConcentratedAtBFLevels (modelsOf (V := ℕ) φ) ∧
        ¬ Countable (Quotient (isoSetoidOn ℕ φ)) := by
  rw [← bfScattered_and_minimallyUncountableOn_modelsOf_iff,
    and_iff_right hthin.bfScattered_modelsOf]

/-- On a back-and-forth scattered class, an isolating rank is bounded below `ω₁` if and only if the
class meets countably many isomorphism classes. -/
theorem IsIsolatingRank.boundedRankOn_iff_countable_isoClasses
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    BoundedRankOn ρ K ↔ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  boundedRankOn_iff.trans <| (hρ.countable_isoClasses_iff_bounded hK).symm.trans
    Setoid.countable_quotient_comap_val_iff

/-- On a back-and-forth scattered class, an isolating rank is unbounded below `ω₁` if and only if
the class meets uncountably many isomorphism classes. -/
theorem IsIsolatingRank.unboundedRankOn_iff_not_countable_isoClasses
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    UnboundedRankOn ρ K ↔ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  unboundedRankOn_iff_not_boundedRankOn.trans
    (not_congr (hρ.boundedRankOn_iff_countable_isoClasses hK))

/-- On a back-and-forth scattered class `K`, minimal unboundedness for any isolating rank `ρ` is
equivalent to minimal uncountability of `K`. Neither definability nor isomorphism invariance of `K`,
nor countability of `L`, is needed. -/
theorem IsIsolatingRank.minimallyUnboundedOn_iff_minimallyUncountableOn
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUncountableOn K := by
  rw [minimallyUnboundedOn_iff, minimallyUncountableOn_iff,
    hρ.unboundedRankOn_iff_not_countable_isoClasses hK]
  refine and_congr_right' (forall_congr' fun θ => or_congr ?_ ?_)
  · exact hρ.boundedRankOn_iff_countable_isoClasses (hK.mono inter_subset_left)
  · exact hρ.boundedRankOn_iff_countable_isoClasses (hK.mono sdiff_subset)

/-- On a back-and-forth scattered class, minimal unboundedness does not depend on which isolating
rank is used. -/
theorem IsIsolatingRank.minimallyUnboundedOn_iff
    {ρ σ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    (hσ : IsIsolatingRank σ) {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn σ K :=
  (hρ.minimallyUnboundedOn_iff_minimallyUncountableOn hK).trans
    (hσ.minimallyUnboundedOn_iff_minimallyUncountableOn hK).symm

/-- On a back-and-forth scattered class, minimal unboundedness of the external Scott height is
equivalent to minimal uncountability. -/
theorem BFScattered.minimallyUnboundedOn_scottHeight_iff_minimallyUncountableOn
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUnboundedOn (fun c => @scottHeight L _ ℕ c.toStructure) K ↔
      MinimallyUncountableOn K :=
  (isIsolatingRank_scottHeight L).minimallyUnboundedOn_iff_minimallyUncountableOn hK

end ConcentrationAndRanks

/-! ### The Harnik–Makkai splitting tree and minimal counterexamples -/

section HarnikMakkai

variable {L : Language.{u, v}} [L.IsRelational]

/-- If a back-and-forth scattered set `S` meets uncountably many isomorphism classes and is a union
of classes of `bfEquivSetoid L ℕ α` at a countable level `α < ω₁`, then `S` contains an entire
level-`α` class that itself meets uncountably many isomorphism classes. -/
theorem BFScattered.exists_bfEquivSetoid_subset_not_countable_isoClasses
    {S : Set (RelationalConfiguration L ℕ)} (hS : BFScattered S)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' S).Countable) {α : Ordinal.{0}} (hα : α < ω₁)
    (hsat : ∀ c ∈ S, ∀ d, bfEquivSetoid L ℕ α c d → d ∈ S) :
    ∃ c ∈ S, {d | bfEquivSetoid L ℕ α c d} ⊆ S ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ α c d}).Countable := by
  classical
  have := hS.countable_quotient hα
  let F (q : Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : S → _))) :=
    {d : RelationalConfiguration L ℕ | bfEquivSetoid L ℕ α q.out.val d}
  have hsub (q) : F q ⊆ S := fun d hd => hsat q.out.val q.out.prop d hd
  have hcover : ⋃ q, F q = S := by
    refine subset_antisymm (iUnion_subset hsub) fun x hx => ?_
    let q : Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : S → _)) := ⟦⟨x, hx⟩⟧
    exact mem_iUnion.2 ⟨q,
      Quotient.exact (s := (bfEquivSetoid L ℕ α).comap (Subtype.val : S → _))
        (Quotient.out_eq q)⟩
  have hex : ∃ q, ¬ (Quotient.mk (isoSetoid L ℕ) '' F q).Countable := by
    by_contra! hall
    exact hunc (hcover ▸ (image_iUnion ▸ countable_iUnion hall))
  obtain ⟨q, hq⟩ := hex
  exact ⟨q.out.val, q.out.prop, hsub q, hq⟩

private structure SplitStage (Θ : L.Sentenceω) (n : ℕ) where
  level : Ordinal.{0}
  level_lt : level < ω₁
  node : (Fin n → Bool) → RelationalConfiguration L ℕ
  subset_modelsOf : ∀ σ, {d | bfEquivSetoid L ℕ level (node σ) d} ⊆ modelsOf Θ
  uncountable_class : ∀ σ,
    ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ level (node σ) d}).Countable

private theorem exists_split_sentence_of_not_minimallyUncountableOn
    [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (hno : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)))
    {c : RelationalConfiguration L ℕ} {α : Ordinal.{0}} (hα : α < ω₁)
    (hsub : {d | bfEquivSetoid L ℕ α c d} ⊆ modelsOf Θ)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ α c d}).Countable) :
    ∃ φ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) ''
        ({d | bfEquivSetoid L ℕ α c d} ∩ modelsOf φ)).Countable ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) ''
        ({d | bfEquivSetoid L ℕ α c d} \ modelsOf φ)).Countable := by
  have hmod : modelsOf (V := ℕ) (Θ ⊓ c.scottSentenceAtLevel α) =
      {d | bfEquivSetoid L ℕ α c d} := by
    rw [modelsOf_inf, modelsOf_scottSentenceAtLevel c hα, inter_eq_self_of_subset_right hsub]
  have hnot : ¬ MinimallyUncountableOn {d | bfEquivSetoid L ℕ α c d} :=
    hmod ▸ hno (c.scottSentenceAtLevel α)
  rw [minimallyUncountableOn_iff, not_and, not_forall] at hnot
  obtain ⟨φ, hφ⟩ := hnot hunc
  exact ⟨φ, not_or.1 hφ⟩

private theorem exists_next_splitStage [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hno : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)))
    {n : ℕ} (s : SplitStage Θ n) :
    ∃ s' : SplitStage Θ (n + 1),
      s.level + Ordinal.omega0 ≤ s'.level ∧
      (∀ τ : Fin (n + 1) → Bool,
        bfEquivSetoid L ℕ s.level (s.node (Fin.init τ)) (s'.node τ)) ∧
      (∀ τ₁ τ₂ : Fin (n + 1) → Bool,
        Fin.init τ₁ = Fin.init τ₂ → τ₁ (Fin.last n) ≠ τ₂ (Fin.last n) →
          ¬ bfEquivSetoid L ℕ s'.level (s'.node τ₁) (s'.node τ₂)) := by
  -- Split each node's level class into two large halves and saturate all `φ σ` at one level `γ`.
  choose φ hφ₀ hφ₁ using fun σ => exists_split_sentence_of_not_minimallyUncountableOn hno
    s.level_lt (s.subset_modelsOf σ) (s.uncountable_class σ)
  obtain ⟨β₀, hβ₀, hsatφ⟩ :=
    exists_bfLevel_forall_saturated_modelsOf.{u, v, 0, 0, 0, 0} (V := ℕ) φ
  let γ : Ordinal.{0} := max (s.level + Ordinal.omega0) β₀
  have hγ : γ < ω₁ :=
    max_lt (Ordinal.isPrincipal_add_omega 1 s.level_lt Ordinal.omega0_lt_omega_one) hβ₀
  have hsle : s.level ≤ γ := (le_add_of_nonneg_right bot_le).trans (le_max_left _ _)
  have hC_sat (σ : Fin n → Bool) {x y} (hx : bfEquivSetoid L ℕ s.level (s.node σ) x)
      (hxy : bfEquivSetoid L ℕ γ x y) : bfEquivSetoid L ℕ s.level (s.node σ) y :=
    (bfEquivSetoid L ℕ s.level).trans hx (bfEquivSetoid_anti hsle hxy)
  -- Pick a large level-`γ` class inside each side of every node's split.
  choose c₀ hc₀_mem hc₀_sub hc₀_unc using fun σ => by
    have hscat₀ : BFScattered ({d | bfEquivSetoid L ℕ s.level (s.node σ) d} ∩ modelsOf (φ σ)) :=
      hK.mono (inter_subset_left.trans (s.subset_modelsOf σ))
    exact hscat₀.exists_bfEquivSetoid_subset_not_countable_isoClasses (hφ₀ σ) hγ fun x hx y hxy =>
      ⟨hC_sat σ hx.1 hxy, (hsatφ γ (le_max_right _ _) σ x y hxy).mp hx.2⟩
  choose c₁ hc₁_mem hc₁_sub hc₁_unc using fun σ => by
    have hscat₁ : BFScattered ({d | bfEquivSetoid L ℕ s.level (s.node σ) d} \ modelsOf (φ σ)) :=
      hK.mono (sdiff_subset.trans (s.subset_modelsOf σ))
    exact hscat₁.exists_bfEquivSetoid_subset_not_countable_isoClasses (hφ₁ σ) hγ fun x hx y hxy =>
      ⟨hC_sat σ hx.1 hxy, fun hy => hx.2 ((hsatφ γ (le_max_right _ _) σ x y hxy).mpr hy)⟩
  let node' (τ : Fin (n + 1) → Bool) : RelationalConfiguration L ℕ :=
    cond (τ (Fin.last n)) (c₁ (Fin.init τ)) (c₀ (Fin.init τ))
  refine ⟨⟨γ, hγ, node', fun τ => ?_, fun τ => ?_⟩, le_max_left _ _, fun τ => ?_,
    fun τ₁ τ₂ hinit hlast heq => ?_⟩
  · dsimp only [node']
    cases τ (Fin.last n)
    · exact (hc₀_sub (Fin.init τ)).trans (inter_subset_left.trans (s.subset_modelsOf _))
    · exact (hc₁_sub (Fin.init τ)).trans (sdiff_subset.trans (s.subset_modelsOf _))
  · dsimp only [node']
    cases τ (Fin.last n)
    · exact hc₀_unc (Fin.init τ)
    · exact hc₁_unc (Fin.init τ)
  · dsimp only [node']
    cases τ (Fin.last n)
    · exact (hc₀_mem (Fin.init τ)).1
    · exact (hc₁_mem (Fin.init τ)).1
  · dsimp only [node'] at heq
    rw [← hinit] at heq
    cases hb₁ : τ₁ (Fin.last n) <;> cases hb₂ : τ₂ (Fin.last n)
    · exact hlast (hb₁.trans hb₂.symm)
    · rw [hb₁, hb₂] at heq
      exact (hc₁_mem (Fin.init τ₁)).2
        ((hsatφ γ (le_max_right _ _) (Fin.init τ₁) _ _ heq).mp (hc₀_mem (Fin.init τ₁)).2)
    · rw [hb₁, hb₂] at heq
      exact (hc₁_mem (Fin.init τ₁)).2
        ((hsatφ γ (le_max_right _ _) (Fin.init τ₁) _ _ heq).mpr (hc₀_mem (Fin.init τ₁)).2)
    · exact hlast (hb₁.trans hb₂.symm)

private theorem exists_limit_family_of_splitStage {Θ : L.Sentenceω}
    (stage : ∀ n, SplitStage Θ n)
    (hstep : ∀ n,
      (stage n).level + Ordinal.omega0 ≤ (stage (n + 1)).level ∧
      (∀ τ : Fin (n + 1) → Bool,
        bfEquivSetoid L ℕ (stage n).level ((stage n).node (Fin.init τ)) ((stage (n + 1)).node τ)) ∧
      (∀ τ₁ τ₂ : Fin (n + 1) → Bool,
        Fin.init τ₁ = Fin.init τ₂ → τ₁ (Fin.last n) ≠ τ₂ (Fin.last n) →
          ¬ bfEquivSetoid L ℕ (stage (n + 1)).level
            ((stage (n + 1)).node τ₁) ((stage (n + 1)).node τ₂))) :
    ∃ lim : (ℕ → Bool) → RelationalConfiguration L ℕ,
      (∀ X, lim X ∈ modelsOf (V := ℕ) Θ) ∧
      ∀ X Y, X ≠ Y →
        ¬ bfEquivSetoid L ℕ (⨆ n : ℕ, (stage n).level) (lim X) (lim Y) := by
  classical
  have hmono : Monotone fun n => (stage n).level :=
    monotone_nat_of_le_succ fun n => (le_add_of_nonneg_right bot_le).trans (hstep n).1
  let res (X : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun j => X j
  choose lim hlim using fun X : ℕ → Bool =>
    exists_limit_of_bfEquiv_chain (c := fun k => (stage (k + 1)).node (res X (k + 1))) hmono
      fun k => bfEquivSetoid_anti (hstep k).1 ((hstep (k + 1)).2.1 (res X (k + 2)))
  refine ⟨lim, fun X => ?_, fun X Y hXY hXY_sup => ?_⟩
  · exact (stage 0).subset_modelsOf (Fin.init (res X 1)) <|
      (bfEquivSetoid L ℕ (stage 0).level).trans ((hstep 0).2.1 (res X 1))
        ((bfEquivSetoid L ℕ (stage 0).level).symm (hlim X 0))
  · have hex : ∃ i, X i ≠ Y i := Function.ne_iff.mp hXY
    let i := Nat.find hex
    have hinit : Fin.init (res X (i + 1)) = Fin.init (res Y (i + 1)) := by
      ext j
      exact not_not.1 (Nat.find_min hex j.isLt)
    have hX : bfEquivSetoid L ℕ (stage (i + 1)).level
        ((stage (i + 1)).node (res X (i + 1))) (lim X) :=
      (bfEquivSetoid L ℕ (stage (i + 1)).level).trans ((hstep (i + 1)).2.1 (res X (i + 2)))
        ((bfEquivSetoid L ℕ (stage (i + 1)).level).symm (hlim X (i + 1)))
    have hY : bfEquivSetoid L ℕ (stage (i + 1)).level
        (lim Y) ((stage (i + 1)).node (res Y (i + 1))) :=
      (bfEquivSetoid L ℕ (stage (i + 1)).level).trans (hlim Y (i + 1))
        ((bfEquivSetoid L ℕ (stage (i + 1)).level).symm ((hstep (i + 1)).2.1 (res Y (i + 2))))
    have hXY_i : bfEquivSetoid L ℕ (stage (i + 1)).level (lim X) (lim Y) :=
      bfEquivSetoid_anti (Ordinal.le_iSup (fun n => (stage n).level) (i + 1)) hXY_sup
    exact (hstep i).2.2 (res X (i + 1)) (res Y (i + 1)) hinit (Nat.find_spec hex)
      ((bfEquivSetoid L ℕ (stage (i + 1)).level).trans hX
        ((bfEquivSetoid L ℕ (stage (i + 1)).level).trans hXY_i hY))

/-- **The Harnik–Makkai reduction.** If the models on `ℕ` of an `L_{ω₁ω}` sentence `Θ` are
back-and-forth scattered and meet uncountably many isomorphism classes, then some strengthening
`Θ ⊓ θ` by an `L_{ω₁ω}` sentence `θ` has minimally uncountable models on `ℕ`. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered [Countable (Σ n, L.Relations n)]
    {Θ : L.Sentenceω} (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  by_contra! hno
  obtain ⟨α₀, hα₀, hsat₀⟩ :=
    exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) Θ
  obtain ⟨c₀, _, hc₀_sub, hc₀_unc⟩ :=
    hK.exists_bfEquivSetoid_subset_not_countable_isoClasses hunc hα₀ fun c hc d hcd =>
      (hsat₀ α₀ le_rfl c d hcd).mp hc
  let s₀ : SplitStage Θ 0 :=
    ⟨α₀, hα₀, fun _ => c₀, fun _ => hc₀_sub, fun _ => hc₀_unc⟩
  let step {n : ℕ} (s : SplitStage Θ n) := exists_next_splitStage hK hno s
  let stage : ∀ n, SplitStage Θ n := Nat.rec s₀ fun _ s => (step s).choose
  obtain ⟨lim, hmem, hsep⟩ :=
    exists_limit_family_of_splitStage stage fun n => (step (stage n)).choose_spec
  let β : Ordinal.{0} := ⨆ n : ℕ, (stage n).level
  have hβ : β < ω₁ := Ordinal.iSup_lt_omega_one fun n => (stage n).level_lt
  let Qβ := Quotient ((bfEquivSetoid L ℕ β).comap (Subtype.val : modelsOf Θ → _))
  have hinj : Function.Injective fun X : ℕ → Bool => (⟦⟨lim X, hmem X⟩⟧ : Qβ) :=
    fun X Y hXY_eq => by_contra fun hXY =>
      hsep X Y hXY
        (Quotient.exact (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : modelsOf Θ → _)) hXY_eq)
  have : Countable Qβ := hK.countable_quotient hβ
  have hcont : 𝔠 ≤ #Qβ := by simpa using lift_mk_le_lift_mk_of_injective hinj
  exact Cardinal.aleph0_lt_continuum.not_ge (hcont.trans mk_le_aleph0)

/-- A thin `L_{ω₁ω}` sentence on `ℕ` with uncountably many models on `ℕ` up to isomorphism has a
strengthening `Θ ⊓ θ` whose models on `ℕ` are minimally uncountable. -/
theorem IsThinOnNatModels.exists_minimallyUncountableOn_inf [Countable (Σ n, L.Relations n)]
    {Θ : L.Sentenceω} (hthin : IsThinOnNatModels Θ)
    (hunc : ¬ Countable (Quotient (isoSetoidOn ℕ Θ))) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) :=
  exists_minimallyUncountableOn_inf_of_bfScattered hthin.bfScattered_modelsOf fun hc =>
    hunc (Setoid.countable_quotient_comap_val_iff.2 hc)

/-- **Rank form of the Harnik–Makkai reduction** (Montalbán, Theorem XII.7). If the models on `ℕ`
of `Θ : L.Sentenceω` are back-and-forth scattered and an isolating rank `ρ` is unbounded below
`ω₁` on them, then some strengthening `Θ ⊓ θ` is minimally unbounded for `ρ` on `ℕ`. -/
theorem exists_minimallyUnboundedOn_inf_of_bfScattered [Countable (Σ n, L.Relations n)]
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {Θ : L.Sentenceω} (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunb : UnboundedRankOn ρ (modelsOf (V := ℕ) Θ)) :
    ∃ θ : L.Sentenceω, MinimallyUnboundedOn ρ (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hK
    ((hρ.unboundedRankOn_iff_not_countable_isoClasses hK).1 hunb)
  have hK' : BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
    rw [modelsOf_inf]
    exact hK.mono inter_subset_left
  exact ⟨θ, (hρ.minimallyUnboundedOn_iff_minimallyUncountableOn hK').2 hmin⟩

end HarnikMakkai

/-! ### Minimal-counterexample formulations of Vaught's conjecture -/

section Vaught

/-- If `modelsOf φ` on `ℕ` is back-and-forth scattered and minimally uncountable, then
`φ ⊓ L.infiniteSentence` fails Vaught's perfect-set dichotomy. -/
theorem BFScattered.not_hasVaughtDichotomy_inf_infiniteSentence_of_minimallyUncountableOn
    {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)] {φ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) φ))
    (hmin : MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    ¬ HasVaughtDichotomy (φ ⊓ L.infiniteSentence) := by
  rw [hasVaughtDichotomy_inf_infiniteSentence_iff, not_or]
  exact ⟨hmin.not_countable_quotient, Setoid.isThinOn_iff.1 hK.isThinOn⟩

/-- A back-and-forth scattered minimally uncountable sentence in a countable relational language in
universe zero refutes `VaughtConjecture`. -/
theorem BFScattered.not_vaughtConjecture_of_minimallyUncountableOn
    {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) φ))
    (hmin : MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    ¬ VaughtConjecture :=
  fun hV => hK.not_hasVaughtDichotomy_inf_infiniteSentence_of_minimallyUncountableOn hmin
    ((vaughtConjecture_iff.1 hV) L (φ ⊓ L.infiniteSentence))

/-- **Minimal-counterexample formulation of Vaught's conjecture (scattered form).** Vaught's
perfect-set conjecture is equivalent, without CH, to the non-existence of a sentence whose models
on `ℕ` are both back-and-forth scattered and minimally uncountable. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      BFScattered (modelsOf (V := ℕ) φ) →
        ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) := by
  constructor
  · intro hV L _ _ φ hscat hmin
    exact hscat.not_vaughtConjecture_of_minimallyUncountableOn hmin hV
  · intro h
    refine vaughtConjecture_iff_bfScattered.2 fun L _ _ Θ hscat => ?_
    by_contra hunc
    have hunc' : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable :=
      fun hc => hunc (Setoid.countable_quotient_comap_val_iff.2 hc)
    obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc'
    have hscat' : BFScattered (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
      rw [modelsOf_inf]
      exact hscat.mono inter_subset_left
    exact h L (Θ ⊓ θ) hscat' hmin

/-- **Minimal-counterexample formulation of Vaught's conjecture (thin form).** Vaught's
perfect-set conjecture is equivalent, without CH, to the non-existence of a thin sentence whose
models on `ℕ` are minimally uncountable. -/
theorem vaughtConjecture_iff_forall_isThinOnNatModels_not_minimallyUncountableOn :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      IsThinOnNatModels φ → ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) := by
  rw [vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn]
  refine forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun φ => imp_congr_left bfScattered_modelsOf_iff_isThinOnNatModels

/-- **Minimal-counterexample formulation of Vaught's conjecture (isolating-rank form).** Vaught's
perfect-set conjecture holds if and only if no back-and-forth scattered sentence is minimally
unbounded on `ℕ` for any isolating rank. -/
theorem vaughtConjecture_iff_forall_bfScattered_not_minimallyUnboundedOn :
    VaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω)
      (ρ : RelationalConfiguration L ℕ → Ordinal.{0}), IsIsolatingRank ρ →
      BFScattered (modelsOf (V := ℕ) φ) →
        ¬ MinimallyUnboundedOn ρ (modelsOf (V := ℕ) φ) := by
  rw [vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn]
  constructor
  · intro h L _ _ φ ρ hρ hscat hmin
    exact h L φ hscat ((hρ.minimallyUnboundedOn_iff_minimallyUncountableOn hscat).1 hmin)
  · intro h L _ _ φ hscat hmin
    exact h L φ _ (isIsolatingRank_scottHeight L) hscat
      (hscat.minimallyUnboundedOn_scottHeight_iff_minimallyUncountableOn.2 hmin)

/-- When `ℵ₁ < 𝔠`, the cardinal Vaught conjecture is equivalent to the non-existence of a
sentence whose models on `ℕ` are both back-and-forth scattered and minimally uncountable. -/
theorem cardinalVaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn
    (hc : ℵ₁ < (𝔠 : Cardinal.{0})) :
    CardinalVaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (φ : L.Sentenceω),
      BFScattered (modelsOf (V := ℕ) φ) →
        ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ) :=
  (cardinalVaughtConjecture_iff_vaughtConjecture hc).trans
    vaughtConjecture_iff_forall_bfScattered_not_minimallyUncountableOn

end Vaught

end TauCeti
