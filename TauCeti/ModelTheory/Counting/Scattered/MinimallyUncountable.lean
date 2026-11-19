/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.AnalyticSplits
public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Vaught

/-!
# Minimally uncountable classes and the Harnik–Makkai reduction

A set `K` of relational configurations on `ℕ` is *minimally uncountable* when it meets uncountably
many isomorphism classes, while every cut of `K` by an `L_{ω₁ω}` sentence has a side meeting only
countably many. For a back-and-forth scattered analytic class this is the same as being
concentrated at back-and-forth levels and meeting uncountably many isomorphism classes.

The main result is the Harnik–Makkai reduction: if a Borel, isomorphism-invariant class `K` is
back-and-forth scattered and meets uncountably many isomorphism classes, then some sentence cut
`K ∩ modelsOf θ` is minimally uncountable. Otherwise every such cut that meets uncountably many
isomorphism classes splits into two sides that both do, and these splittings build a binary tree
of back-and-forth classes. Each level class is cut out by a Scott sentence at that level; each
splitting sentence is decided by back-and-forth equivalence from some countable level on; and the
nodes along each branch form a back-and-forth chain whose limit configuration lies in `K`. The
limits of distinct branches are inequivalent at one countable level, so `K` meets continuum many
classes at that level, contradicting scatteredness.

Applied to the models on `ℕ` of a counterexample to Vaught's dichotomy, which are back-and-forth
scattered, the reduction shows that every counterexample has a minimally uncountable
strengthening. Hence Vaught's conjecture holds as soon as no sentence has minimally uncountable
models on `ℕ`.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes, and every
  sentence cut of `K` has a side meeting only countably many.

## Main results

* `TauCeti.minimallyUncountableOn_iff_concentratedAtBFLevels`: an analytic, back-and-forth
  scattered class is minimally uncountable exactly when it is concentrated at back-and-forth
  levels and meets uncountably many isomorphism classes.
* `TauCeti.exists_minimallyUncountableOn_inter_modelsOf`: the Harnik–Makkai reduction for a
  Borel, isomorphism-invariant, back-and-forth scattered class meeting uncountably many
  isomorphism classes.
* `TauCeti.exists_minimallyUncountableOn_modelsOf_inf`: the sentence form, a strengthening
  `Θ ⊓ θ` with minimally uncountable models on `ℕ`.
* `TauCeti.exists_minimallyUncountableOn_modelsOf_inf_of_not_hasVaughtDichotomy` and
  `TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`: every counterexample to
  Vaught's dichotomy has a minimally uncountable strengthening.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proceedings of the
  American Mathematical Society 67 (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689
  (1978), 193–208.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2: the limit model (Lemma XII.6) and the splitting-tree argument of Theorem XII.7. Here the
  splitting sentences are made level-saturated by uniform back-and-forth separation rather than by
  their quantifier complexity.
* Minimally uncountable classes and their characterization through concentration are also
  formalized in Cameron Freer's `cameronfreer/infinitary-logic`,
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` (checkpoint `518a366`, Apache-2.0). That
  development does not contain the splitting tree or the reduction to minimal counterexamples.
-/

public section

universe u v

open FirstOrder FirstOrder.Language Cardinal Ordinal Set MeasureTheory

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {K : Set (RelationalConfiguration L ℕ)}

/-- A set `K` of configurations on `ℕ` is *minimally uncountable* when it meets uncountably many
isomorphism classes, and for every `L_{ω₁ω}` sentence `θ` one of `K ∩ modelsOf θ` and
`K \ modelsOf θ` meets only countably many. The cuts range over sentences, not over arbitrary
isomorphism-invariant sets. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L ℕ)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
    ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable

/-- Unfolding lemma for `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff : MinimallyUncountableOn K ↔
    ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
      ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- The models on `ℕ` of a sentence `φ` are minimally uncountable exactly when they meet
uncountably many isomorphism classes, and for every sentence `θ` the models of `φ ⊓ θ` or those
of `φ ⊓ θ.not` meet only countably many. -/
theorem minimallyUncountableOn_modelsOf_iff_inf {φ : L.Sentenceω} :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔
      ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf φ).Countable ∧
        ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L ℕ) '' modelsOf (φ ⊓ θ)).Countable ∨
          (Quotient.mk (isoSetoid L ℕ) '' modelsOf (φ ⊓ θ.not)).Countable := by
  simp only [minimallyUncountableOn_iff, modelsOf_inf, modelsOf_not, sdiff_eq]

/-- The empty class is not minimally uncountable: it meets no isomorphism class. -/
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L ℕ)) :=
  fun h => h.1 (by simp)

/-- A back-and-forth scattered, minimally uncountable class is concentrated at back-and-forth
levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    (h : MinimallyUncountableOn K) (hK : BFScattered K) : ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK h.2

/-- An analytic class that is concentrated at back-and-forth levels and meets uncountably many
isomorphism classes is minimally uncountable. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn [∀ n, Countable (L.Relations n)]
    (hC : ConcentratedAtBFLevels K) (hKa : AnalyticSet K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) : MinimallyUncountableOn K :=
  ⟨hunc, fun θ => by
    simpa only [Setoid.countable_quotient_comap_val_iff] using
      hC.countable_isoClasses_inter_modelsOf_or_sdiff hKa θ⟩

/-- An analytic, back-and-forth scattered class is minimally uncountable exactly when it is
concentrated at back-and-forth levels and meets uncountably many isomorphism classes. -/
theorem minimallyUncountableOn_iff_concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    (hKa : AnalyticSet K) (hK : BFScattered K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun h => ⟨h.concentratedAtBFLevels hK, h.1⟩,
    fun h => h.1.minimallyUncountableOn hKa h.2⟩

/-! ### The splitting tree -/

/-- A binary tree of configurations with levels, indexed by words read from their most recent
letter: the node `T (b :: σ)` is the child `b` of `T σ`. Levels are countable and grow by at
least `ω` from a node to its children, both children of a node share their level, each child is
equivalent to its parent at the parent's level, and the two children are inequivalent at their
own level. -/
private structure IsSplittingTree (T : List Bool → RelationalConfiguration L ℕ × Ordinal.{0}) :
    Prop where
  level_lt (σ : List Bool) : (T σ).2 < ω₁
  add_omega_le (σ : List Bool) (b : Bool) : (T σ).2 + ω ≤ (T (b :: σ)).2
  level_cons (σ : List Bool) (b b' : Bool) : (T (b :: σ)).2 = (T (b' :: σ)).2
  bfEquiv_cons (σ : List Bool) (b : Bool) : bfEquivSetoid L ℕ (T σ).2 (T σ).1 (T (b :: σ)).1
  not_bfEquiv (σ : List Bool) :
    ¬ bfEquivSetoid L ℕ (T (true :: σ)).2 (T (true :: σ)).1 (T (false :: σ)).1

/-- A splitting tree grows from any node satisfying a predicate that bounds levels below `ω₁` and
that always admits a splitting step. -/
private theorem exists_isSplittingTree (P : RelationalConfiguration L ℕ → Ordinal.{0} → Prop)
    (hlt : ∀ A α, P A α → α < ω₁)
    (hstep : ∀ A α, P A α → ∃ α' : Ordinal.{0}, ∃ A' : Bool → RelationalConfiguration L ℕ,
      (∀ b, P (A' b) α') ∧ α + ω ≤ α' ∧ (∀ b, bfEquivSetoid L ℕ α A (A' b)) ∧
        ¬ bfEquivSetoid L ℕ α' (A' true) (A' false))
    {A : RelationalConfiguration L ℕ} {α : Ordinal.{0}} (hA : P A α) :
    ∃ T, T [] = (A, α) ∧ IsSplittingTree T := by
  have h (t : RelationalConfiguration L ℕ × Ordinal.{0}) :
      ∃ s : Ordinal.{0} × (Bool → RelationalConfiguration L ℕ), P t.1 t.2 →
        (∀ b, P (s.2 b) s.1) ∧ t.2 + ω ≤ s.1 ∧ (∀ b, bfEquivSetoid L ℕ t.2 t.1 (s.2 b)) ∧
          ¬ bfEquivSetoid L ℕ s.1 (s.2 true) (s.2 false) := by
    by_cases hP : P t.1 t.2
    · obtain ⟨α', A', hA'⟩ := hstep t.1 t.2 hP
      exact ⟨(α', A'), fun _ => hA'⟩
    · exact ⟨(0, fun _ => t.1), fun h => absurd h hP⟩
  choose next hnext using h
  let T (σ : List Bool) : RelationalConfiguration L ℕ × Ordinal.{0} :=
    σ.foldr (fun b t => ((next t).2 b, (next t).1)) (A, α)
  have hT (σ : List Bool) (b : Bool) : T (b :: σ) = ((next (T σ)).2 b, (next (T σ)).1) :=
    List.foldr_cons
  have hP (σ : List Bool) : P (T σ).1 (T σ).2 := by
    induction σ with
    | nil => exact hA
    | cons b σ ih => simpa only [hT] using (hnext _ ih).1 b
  refine ⟨T, List.foldr_nil, fun σ => hlt _ _ (hP σ), fun σ b => ?_, fun σ b b' => ?_,
    fun σ b => ?_, fun σ => ?_⟩
  · rw [hT]
    exact (hnext _ (hP σ)).2.1
  · rw [hT, hT]
  · rw [hT]
    exact (hnext _ (hP σ)).2.2.1 b
  · rw [hT, hT]
    exact (hnext _ (hP σ)).2.2.2

namespace IsSplittingTree

variable {T : List Bool → RelationalConfiguration L ℕ × Ordinal.{0}}

/-- The two children of a node are inequivalent at their common level, in either order. -/
private theorem not_bfEquiv_of_ne (hT : IsSplittingTree T) (σ : List Bool) {b b' : Bool}
    (hb : b ≠ b') : ¬ bfEquivSetoid L ℕ (T (b :: σ)).2 (T (b :: σ)).1 (T (b' :: σ)).1 := by
  cases b <;> cases b'
  · exact absurd rfl hb
  · rw [hT.level_cons σ false true]
    exact fun h => hT.not_bfEquiv σ ((bfEquivSetoid L ℕ _).symm h)
  · exact hT.not_bfEquiv σ
  · exact absurd rfl hb

/-- **Limits along the branches of a splitting tree.** Every branch `x : ℕ → Bool` of a splitting
tree has a limit configuration, equivalent to the root at the root's level, and the limits of
distinct branches are inequivalent at one countable level `β`. -/
private theorem exists_injective_limits (hT : IsSplittingTree T) :
    ∃ β : Ordinal.{0}, β < ω₁ ∧ ∃ d : (ℕ → Bool) → RelationalConfiguration L ℕ,
      (∀ x, bfEquivSetoid L ℕ (T []).2 (T []).1 (d x)) ∧
        ∀ x y, bfEquivSetoid L ℕ β (d x) (d y) → x = y := by
  -- the node of the branch `x` at depth `n` is `T (pre x n)`
  let pre (x : ℕ → Bool) (n : ℕ) : List Bool := ((List.range n).reverse).map x
  have hpre (x : ℕ → Bool) (n : ℕ) : pre x (n + 1) = x n :: pre x n := by
    simp [pre, List.range_succ]
  -- each branch is a back-and-forth chain, with a limit `d x`
  have hlim (x : ℕ → Bool) :
      ∃ d, ∀ i, bfEquivSetoid L ℕ (T (pre x i)).2 d (T (pre x (i + 1))).1 := by
    refine exists_limit_of_bfEquiv_chain (monotone_nat_of_le_succ fun i => ?_) fun i => ?_
    · rw [hpre]
      exact le_self_add.trans (hT.add_omega_le _ _)
    · rw [hpre x (i + 1)]
      refine bfEquivSetoid_anti ?_ (hT.bfEquiv_cons _ _)
      rw [hpre]
      exact hT.add_omega_le _ _
  choose d hd using hlim
  -- the limit of a branch is equivalent to each node of the branch at that node's level
  have hnode (x : ℕ → Bool) (n : ℕ) :
      bfEquivSetoid L ℕ (T (pre x (n + 1))).2 (T (pre x (n + 1))).1 (d x) := by
    have h := hd x (n + 1)
    rw [hpre x (n + 1)] at h
    exact (bfEquivSetoid L ℕ _).trans (hT.bfEquiv_cons _ _) ((bfEquivSetoid L ℕ _).symm h)
  refine ⟨⨆ σ, (T σ).2, Ordinal.iSup_lt_omega_one hT.level_lt, d, fun x => ?_,
    fun x y hxy => ?_⟩
  · have h := hd x 0
    rw [hpre] at h
    exact (bfEquivSetoid L ℕ _).trans (hT.bfEquiv_cons _ _) ((bfEquivSetoid L ℕ _).symm h)
  -- two branches through equivalent limits never part ways
  have hpref (n : ℕ) : pre x n = pre y n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hxy' : x n = y n := by
        by_contra hne
        have hx := hnode x n
        have hy := hnode y n
        rw [hpre, ih] at hx
        rw [hpre, hT.level_cons _ (y n) (x n)] at hy
        refine hT.not_bfEquiv_of_ne (pre y n) hne ((bfEquivSetoid L ℕ _).trans hx
          ((bfEquivSetoid L ℕ _).trans ?_ ((bfEquivSetoid L ℕ _).symm hy)))
        exact bfEquivSetoid_anti (Ordinal.le_iSup (fun σ => (T σ).2) _) hxy
      rw [hpre, hpre, ih, hxy']
  funext n
  have h := hpref (n + 1)
  rw [hpre, hpre] at h
  exact (List.cons.inj h).1

end IsSplittingTree

variable [Countable (Σ n, L.Relations n)]

/-- **One splitting step.** Let `K` be back-and-forth scattered, with no minimally uncountable
sentence cut. If the level-`α` class of `A` meets `K` in uncountably many isomorphism classes,
then at some countable level `α' ≥ α + ω` there are two configurations, both level-`α`
equivalent to `A` and inequivalent to each other at level `α'`, whose level-`α'` classes again
meet `K` in uncountably many isomorphism classes. -/
private theorem exists_splitting_step (hK : BFScattered K)
    (hmin : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (K ∩ modelsOf θ))
    {A : RelationalConfiguration L ℕ} {α : Ordinal.{0}} (hα : α < ω₁)
    (hA : ¬ (Quotient.mk (isoSetoid L ℕ) '' (K ∩ {d | bfEquivSetoid L ℕ α A d})).Countable) :
    ∃ α' : Ordinal.{0}, ∃ A' : Bool → RelationalConfiguration L ℕ,
      (∀ b, α' < ω₁ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
        (K ∩ {d | bfEquivSetoid L ℕ α' (A' b) d})).Countable) ∧
      α + ω ≤ α' ∧ (∀ b, bfEquivSetoid L ℕ α A (A' b)) ∧
        ¬ bfEquivSetoid L ℕ α' (A' true) (A' false) := by
  set C := K ∩ {d | bfEquivSetoid L ℕ α A d}
  -- the level class is a sentence cut, so some sentence `φ` splits it into two large sides
  have hsplit := hmin (A.scottSentenceAtLevel α)
  rw [modelsOf_scottSentenceAtLevel A hα, minimallyUncountableOn_iff] at hsplit
  push Not at hsplit
  obtain ⟨φ, hφ, hnφ⟩ := hsplit hA
  -- from some countable level on, back-and-forth equivalence decides `φ`
  obtain ⟨β, hβ, hsat⟩ := exists_bfLevel_mem_iff_of_measurableSet (V := ℕ) (C := univ)
    MeasurableSet.univ.analyticSet (measurableSet_modelsOf φ) fun _ _ _ _ hcd =>
      ((isomorphismInvariant_modelsOf φ).mem_iff hcd).1
  set α' := max (α + ω) β
  have hα' : α' < ω₁ :=
    max_lt (isPrincipal_add_omega 1 hα omega0_lt_omega_one) hβ
  -- each side has a large level-`α'` class
  have : Countable (Quotient ((bfEquivSetoid L ℕ α').comap
      (Subtype.val : ↥(C ∩ modelsOf φ) → _))) :=
    (hK.mono (inter_subset_left.trans inter_subset_left)).countable_quotient hα'
  obtain ⟨A₀, hA₀, hA₀l⟩ := exists_bfClass_uncountable_isoClasses hφ (α := α')
  have : Countable (Quotient ((bfEquivSetoid L ℕ α').comap
      (Subtype.val : ↥(C \ modelsOf φ) → _))) :=
    (hK.mono (sdiff_subset.trans inter_subset_left)).countable_quotient hα'
  obtain ⟨A₁, hA₁, hA₁l⟩ := exists_bfClass_uncountable_isoClasses hnφ (α := α')
  refine ⟨α', fun b => cond b A₀ A₁, Bool.forall_bool.2 ⟨⟨hα', fun h => hA₁l (h.mono ?_)⟩,
    ⟨hα', fun h => hA₀l (h.mono ?_)⟩⟩, le_max_left _ _, Bool.forall_bool.2 ⟨hA₁.1.2, hA₀.1.2⟩,
    fun h => hA₁.2 ((hsat α' (le_max_right _ _) A₀ trivial A₁ trivial h).1 hA₀.2)⟩
  · exact image_mono fun _ hd => ⟨hd.1.1.1, hd.2⟩
  · exact image_mono fun _ hd => ⟨hd.1.1.1, hd.2⟩

/-- **The Harnik–Makkai reduction.** A Borel, isomorphism-invariant class of configurations on `ℕ`
that is back-and-forth scattered and meets uncountably many isomorphism classes has a minimally
uncountable sentence cut. -/
theorem exists_minimallyUncountableOn_inter_modelsOf (hKm : MeasurableSet K)
    (hKi : IsomorphismInvariant K) (hK : BFScattered K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (K ∩ modelsOf θ) := by
  by_contra! hmin
  -- from some countable level `α₀` on, back-and-forth equivalence preserves membership in `K`
  obtain ⟨α₀, hα₀, hsat⟩ := exists_bfLevel_mem_iff_of_measurableSet (V := ℕ) (C := univ)
    MeasurableSet.univ.analyticSet hKm fun _ _ _ _ hcd => (hKi.mem_iff hcd).1
  -- the root: a level-`α₀` class meeting `K` in uncountably many isomorphism classes
  have := hK.countable_quotient hα₀
  obtain ⟨A, hAK, hA⟩ := exists_bfClass_uncountable_isoClasses hunc (α := α₀)
  obtain ⟨T, hT₀, hT⟩ := exists_isSplittingTree
    (fun A α => α < ω₁ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
      (K ∩ {d | bfEquivSetoid L ℕ α A d})).Countable)
    (fun _ _ h => h.1) (fun _ _ h => exists_splitting_step hK hmin h.1 h.2) ⟨hα₀, hA⟩
  obtain ⟨β, hβ, d, hroot, hinj⟩ := hT.exists_injective_limits
  rw [hT₀] at hroot
  have hdK (x : ℕ → Bool) : d x ∈ K := (hsat α₀ le_rfl A trivial (d x) trivial (hroot x)).1 hAK
  -- the limits of distinct branches are distinct level-`β` classes of `K`
  have := hK.countable_quotient hβ
  have hc : Countable (ℕ → Bool) := Function.Injective.countable
    (f := fun x => (⟦⟨d x, hdK x⟩⟧ : Quotient ((bfEquivSetoid L ℕ β).comap
      (Subtype.val : K → _)))) fun x y hxy =>
        hinj x y (Quotient.exact (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)) hxy)
  rw [← mk_le_aleph0_iff] at hc
  exact hc.not_gt (by simpa using aleph0_lt_continuum)

/-- **The Harnik–Makkai reduction for sentences.** If the models on `ℕ` of `Θ` are back-and-forth
scattered and meet uncountably many isomorphism classes, some strengthening `Θ ⊓ θ` has
minimally uncountable models on `ℕ`. -/
theorem exists_minimallyUncountableOn_modelsOf_inf {Θ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  simpa only [modelsOf_inf] using exists_minimallyUncountableOn_inter_modelsOf
    (measurableSet_modelsOf Θ) (isomorphismInvariant_modelsOf Θ) hK hunc

/-- Every counterexample `φ` to Vaught's dichotomy has a strengthening `φ ⊓ θ` with minimally
uncountable models on `ℕ`. -/
theorem exists_minimallyUncountableOn_modelsOf_inf_of_not_hasVaughtDichotomy {φ : L.Sentenceω}
    (h : ¬ HasVaughtDichotomy φ) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (φ ⊓ θ)) :=
  exists_minimallyUncountableOn_modelsOf_inf (bfScattered_modelsOf_of_not_hasVaughtDichotomy h)
    (Setoid.countable_quotient_comap_val_iff.not.1
      (not_countable_quotient_isoSetoidOn_nat_of_not_hasVaughtDichotomy h))

/-- Vaught's conjecture holds if no sentence of a countable relational language has minimally
uncountable models on `ℕ`. -/
theorem vaughtConjecture_of_forall_not_minimallyUncountableOn
    (h : ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
      (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    VaughtConjecture := by
  refine vaughtConjecture_iff.2 fun L _ _ φ => ?_
  by_contra hφ
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_modelsOf_inf_of_not_hasVaughtDichotomy hφ
  exact h L (φ ⊓ θ) hθ

end TauCeti
