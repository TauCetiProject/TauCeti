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
# Minimally uncountable classes and the reduction to minimal counterexamples

A set `K` of relational configurations on `ℕ` is *minimally uncountable* when it meets
uncountably many isomorphism classes, while every sentence cut of it has a side meeting only
countably many. A sentence with minimally uncountable models is the classical candidate for a
minimal counterexample to Vaught's conjecture.

The main theorem is the reduction of Harnik and Makkai: if the models on `ℕ` of a sentence `Θ`
are back-and-forth scattered and meet uncountably many isomorphism classes, then some
strengthening `Θ ⊓ θ` has minimally uncountable models on `ℕ`. Otherwise one builds a binary
splitting tree of large back-and-forth classes inside the models of `Θ`, each node splitting
into two children that are inequivalent at a common higher level, and the limits of its
branches give continuum many classes at one countable level, against scatteredness.
The ingredients are three facts about the back-and-forth levels: level classes are cut out by
sentences (`modelsOf_scottSentenceAtLevel`); every sentence is saturated from some countable
level on (`exists_bfLevel_saturated_modelsOf`, from its quantifier rank); and a
chain of codes equivalent at levels `α i + ω` has a limit code (`exists_limit_of_bfEquiv_chain`).
No continuum hypothesis and no continuity of the branch limits is used.

Consequently a counterexample to Vaught's conjecture has a strengthening with minimally
uncountable models, so Vaught's conjecture holds as soon as no sentence has minimally uncountable
models on `ℕ`.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes, and every
  sentence cut of `K` has a side meeting countably many.

## Main results

* `TauCeti.minimallyUncountableOn_modelsOf_iff`: the models on `ℕ` of `φ` are minimally
  uncountable exactly when `φ` has uncountably many models up to isomorphism and, for every
  sentence `θ`, one of `φ ⊓ θ` and `φ ⊓ θ.not` has countably many.
* `TauCeti.MinimallyUncountableOn.concentratedAtBFLevels`: a scattered minimally uncountable set
  is concentrated at back-and-forth levels.
* `TauCeti.ConcentratedAtBFLevels.minimallyUncountableOn`: a concentrated set meeting uncountably
  many isomorphism classes is minimally uncountable.
* `TauCeti.minimallyUncountableOn_iff_concentratedAtBFLevels`: on a scattered set, minimal
  uncountability is concentration together with uncountably many isomorphism classes.
* `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`: the Harnik–Makkai reduction.
* `TauCeti.exists_minimallyUncountableOn_inf_of_not_hasVaughtDichotomy`: every counterexample to
  the perfect-set dichotomy has a minimally uncountable strengthening.
* `TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`: if no sentence has minimally
  uncountable models on `ℕ`, then Vaught's conjecture holds.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proceedings of the
  American Mathematical Society 67 (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689,
  Springer, 1978, 193–208.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2 (Theorem XII.7, whose splitting-tree proof is followed here).
-/

public section

universe u v

open FirstOrder FirstOrder.Language Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- A set `K` of configurations on `ℕ` is *minimally uncountable* when it meets uncountably many
isomorphism classes, while for every sentence `θ` one of `K ∩ modelsOf θ` and `K \ modelsOf θ`
meets only countably many. The cuts range over sentences, not over arbitrary invariant sets. -/
def MinimallyUncountableOn (K : Set (RelationalConfiguration L ℕ)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
    ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable

/-- Unfolding lemma for `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff {K : Set (RelationalConfiguration L ℕ)} :
    MinimallyUncountableOn K ↔ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable ∧
      ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L ℕ) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L ℕ) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- A minimally uncountable set meets uncountably many isomorphism classes. -/
theorem MinimallyUncountableOn.not_countable_image {K : Set (RelationalConfiguration L ℕ)}
    (h : MinimallyUncountableOn K) : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  h.1

/-- A minimally uncountable set meets uncountably many isomorphism classes, in quotient form. -/
theorem MinimallyUncountableOn.uncountable_isoClasses {K : Set (RelationalConfiguration L ℕ)}
    (h : MinimallyUncountableOn K) :
    Uncountable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → _))) := by
  rw [uncountable_iff_not_countable, Setoid.countable_quotient_comap_val_iff]
  exact h.1

/-- A minimally uncountable set is nonempty. -/
theorem MinimallyUncountableOn.nonempty {K : Set (RelationalConfiguration L ℕ)}
    (h : MinimallyUncountableOn K) : K.Nonempty := by
  by_contra hK
  rw [not_nonempty_iff_eq_empty] at hK
  exact h.1 (by simp [hK])

/-- Every sentence cut of a minimally uncountable set has a side meeting countably many
isomorphism classes. -/
theorem MinimallyUncountableOn.countable_isoClasses_inter_modelsOf_or_sdiff
    {K : Set (RelationalConfiguration L ℕ)} (h : MinimallyUncountableOn K) (θ : L.Sentenceω) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(K ∩ modelsOf θ) → _))) ∨
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : ↥(K \ modelsOf θ) → _))) := by
  simpa only [Setoid.countable_quotient_comap_val_iff] using h.2 θ

/-- A set meeting countably many isomorphism classes is not minimally uncountable. -/
theorem not_minimallyUncountableOn_of_countable_image {K : Set (RelationalConfiguration L ℕ)}
    (hK : (Quotient.mk (isoSetoid L ℕ) '' K).Countable) : ¬ MinimallyUncountableOn K :=
  fun h => h.1 hK

/-- The empty set is not minimally uncountable. -/
@[simp]
theorem not_minimallyUncountableOn_empty :
    ¬ MinimallyUncountableOn (∅ : Set (RelationalConfiguration L ℕ)) :=
  not_minimallyUncountableOn_of_countable_image (by simp)

/-- The models on `ℕ` of `φ` are minimally uncountable exactly when `φ` has uncountably many models
on `ℕ` up to isomorphism and, for every sentence `θ`, one of `φ ⊓ θ` and `φ ⊓ θ.not` has only
countably many. -/
theorem minimallyUncountableOn_modelsOf_iff {φ : L.Sentenceω} :
    MinimallyUncountableOn (modelsOf (V := ℕ) φ) ↔ Uncountable (Quotient (isoSetoidOn ℕ φ)) ∧
      ∀ θ : L.Sentenceω, Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ))) ∨
        Countable (Quotient (isoSetoidOn ℕ (φ ⊓ θ.not))) := by
  simp only [minimallyUncountableOn_iff, isoSetoidOn, uncountable_iff_not_countable,
    Setoid.countable_quotient_comap_val_iff, modelsOf_inf, modelsOf_not, sdiff_eq]

/-- A back-and-forth scattered, minimally uncountable set is concentrated at back-and-forth
levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (h : MinimallyUncountableOn K) (hK : BFScattered K) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK h.2

/-- A set that is concentrated at back-and-forth levels and meets uncountably many isomorphism
classes is minimally uncountable, since every sentence cut of a concentrated set has a side
meeting countably many isomorphism classes. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn {K : Set (RelationalConfiguration L ℕ)}
    (hK : ConcentratedAtBFLevels K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    MinimallyUncountableOn K :=
  ⟨hunc, fun θ => by
    simpa only [Setoid.countable_quotient_comap_val_iff] using
      hK.countable_isoClasses_inter_modelsOf_or_sdiff θ⟩

/-- A back-and-forth scattered set is minimally uncountable exactly when it is concentrated at
back-and-forth levels and meets uncountably many isomorphism classes. -/
theorem minimallyUncountableOn_iff_concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun h => ⟨h.concentratedAtBFLevels hK, h.1⟩, fun h => h.1.minimallyUncountableOn h.2⟩

/-- **Binary splitting trees.** If some code and level satisfy `P`, and every such pair `(A, α)`
has two children satisfying `P` at a common level `α' ≥ α + ω`, both in the level-`α` class of `A`
and inequivalent at level `α'`, then these choices assemble into a tree indexed by finite binary
words, the children of a word `σ` being `false :: σ` and `true :: σ`. -/
private theorem exists_splitting_tree (P : RelationalConfiguration L ℕ → Ordinal.{0} → Prop)
    (hroot : ∃ A α, P A α)
    (hsplit : ∀ A α, P A α → ∃ α', α + ω ≤ α' ∧ ∃ A₀ A₁, P A₀ α' ∧ P A₁ α' ∧
      bfEquivSetoid L ℕ α A A₀ ∧ bfEquivSetoid L ℕ α A A₁ ∧ ¬ bfEquivSetoid L ℕ α' A₀ A₁) :
    ∃ (A : List Bool → RelationalConfiguration L ℕ) (α : List Bool → Ordinal.{0}),
      (∀ σ, P (A σ) (α σ)) ∧ (∀ σ b, α σ + ω ≤ α (b :: σ)) ∧
      (∀ σ b, bfEquivSetoid L ℕ (α σ) (A σ) (A (b :: σ))) ∧
      (∀ σ, α (false :: σ) = α (true :: σ)) ∧
      ∀ σ, ¬ bfEquivSetoid L ℕ (α (true :: σ)) (A (false :: σ)) (A (true :: σ)) := by
  let Node := {p : RelationalConfiguration L ℕ × Ordinal.{0} // P p.1 p.2}
  choose lvl hlvl code₀ code₁ hP₀ hP₁ hrel₀ hrel₁ hne using
    fun n : Node => hsplit n.val.1 n.val.2 n.property
  let code (n : Node) (b : Bool) : RelationalConfiguration L ℕ := bif b then code₁ n else code₀ n
  have hcodeP (n : Node) (b : Bool) : P (code n b) (lvl n) := by cases b <;> simp [code, *]
  have hcode (n : Node) (b : Bool) : bfEquivSetoid L ℕ n.val.2 n.val.1 (code n b) := by
    cases b <;> simp [code, *]
  obtain ⟨A, α, hroot⟩ := hroot
  -- the node of a word `b :: σ` is the child `b` of the node of `σ`
  let node (σ : List Bool) : Node :=
    σ.foldr (fun b n => ⟨(code n b, lvl n), hcodeP n b⟩) ⟨(A, α), hroot⟩
  exact ⟨fun σ => (node σ).val.1, fun σ => (node σ).val.2, fun σ => (node σ).property,
    fun σ _ => hlvl (node σ), fun σ b => hcode (node σ) b, fun _ => rfl, fun σ => hne (node σ)⟩

/-- **No splitting tree in a scattered set.** Let a back-and-forth scattered set `K` contain the
level-`α σ` class of `A σ` for every finite binary word `σ`, where the levels are countable. If
each child of `σ` lies in the level class of `σ` at a level at least `α σ + ω`, and the two
children of `σ` share their level and are inequivalent at it, we reach a contradiction: the
limits of the branches of the tree lie in `K` and are pairwise inequivalent at the supremum of
the levels of the tree. -/
private theorem false_of_splitting_tree {K : Set (RelationalConfiguration L ℕ)}
    (hK : BFScattered K) (A : List Bool → RelationalConfiguration L ℕ)
    (α : List Bool → Ordinal.{0}) (hlt : ∀ σ, α σ < ω₁)
    (hsub : ∀ σ d, bfEquivSetoid L ℕ (α σ) (A σ) d → d ∈ K)
    (hlvl : ∀ σ b, α σ + ω ≤ α (b :: σ))
    (hchild : ∀ σ b, bfEquivSetoid L ℕ (α σ) (A σ) (A (b :: σ)))
    (hsame : ∀ σ, α (false :: σ) = α (true :: σ))
    (hne : ∀ σ, ¬ bfEquivSetoid L ℕ (α (true :: σ)) (A (false :: σ)) (A (true :: σ))) :
    False := by
  -- the branch through `X` passes through the reversed prefixes `PiNat.res X i`; choose its limit
  choose d hd using fun X => exists_bfEquiv_of_chain (c := fun i => A (PiNat.res X i))
    (α := fun i => α (PiNat.res X i)) (fun i => hlvl _ (X i)) (fun i => hchild _ (X i))
  have hdK (X : ℕ → Bool) : d X ∈ K := hsub _ _ ((bfEquivSetoid L ℕ _).symm (hd X 0))
  -- every level of the tree lies below the countable ordinal `β`
  let β := ⨆ σ, α σ
  have hβ : β < ω₁ := iSup_lt_omega_one hlt
  -- branch limits are inequivalent at level `β`
  have hinj : Function.Injective fun X : ℕ → Bool =>
      (⟦⟨d X, hdK X⟩⟧ : Quotient ((bfEquivSetoid L ℕ β).comap (Subtype.val : K → _))) := by
    intro X Y hXY
    have hXY : bfEquivSetoid L ℕ β (d X) (d Y) :=
      Quotient.exact (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)) hXY
    by_contra hXY'
    -- the branches pass through a common word `σ`, then through its two different children
    let i := PiNat.firstDiff X Y
    have hagree : PiNat.res X i = PiNat.res Y i :=
      PiNat.res_eq_res.2 fun _ hj => PiNat.apply_eq_of_lt_firstDiff hj
    set σ := PiNat.res X i
    have hlvlσ (b : Bool) : α (b :: σ) = α (true :: σ) := by cases b <;> simp [hsame]
    have hX : bfEquivSetoid L ℕ (α (true :: σ)) (d X) (A (X i :: σ)) := by
      have h : bfEquivSetoid L ℕ (α (X i :: σ)) (d X) (A (X i :: σ)) := hd X (i + 1)
      rwa [hlvlσ] at h
    have hY : bfEquivSetoid L ℕ (α (true :: σ)) (d Y) (A (Y i :: σ)) := by
      have h : bfEquivSetoid L ℕ (α (Y i :: PiNat.res Y i)) (d Y) (A (Y i :: PiNat.res Y i)) :=
        hd Y (i + 1)
      rwa [← hagree, hlvlσ] at h
    have hXY := (bfEquivSetoid L ℕ _).trans ((bfEquivSetoid L ℕ _).symm hX)
      ((bfEquivSetoid L ℕ _).trans (bfEquivSetoid_anti (Ordinal.le_iSup α _) hXY) hY)
    have hXi : X i ≠ Y i := PiNat.apply_firstDiff_ne hXY'
    cases hx : X i <;> cases hy : Y i <;> simp only [hx, hy] at hXi hXY
    · exact hXi rfl
    · exact hne σ hXY
    · exact hne σ ((bfEquivSetoid L ℕ _).symm hXY)
    · exact hXi rfl
  have hmk : #(ℕ → Bool) = 𝔠 := by simp
  have := hK.countable_quotient hβ
  have : Countable (ℕ → Bool) := hinj.countable
  exact aleph0_lt_continuum.not_ge (hmk ▸ mk_le_aleph0)

/-- **One splitting step.** Suppose that the models on `ℕ` of `Θ` are back-and-forth scattered and
that no strengthening of `Θ` has minimally uncountable models. If the level-`α` class of `A`
meets the models of `Θ` in uncountably many isomorphism classes, it contains two models `A₀` and
`A₁` of `Θ` that are inequivalent at a countable level `α' ≥ α + ω`, and whose level-`α'` classes
again meet the models of `Θ` in uncountably many isomorphism classes. -/
private theorem exists_bfClass_split [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}
    (hscat : BFScattered (modelsOf (V := ℕ) Θ))
    (hmin : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)))
    {A : RelationalConfiguration L ℕ} {α : Ordinal.{0}} (hα : α < ω₁)
    (hlarge : ¬ (Quotient.mk (isoSetoid L ℕ) ''
      (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α A d})).Countable) :
    ∃ α', α + ω ≤ α' ∧ α' < ω₁ ∧ ∃ A₀ A₁,
      (A₀ ∈ modelsOf Θ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
        (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α' A₀ d})).Countable) ∧
      (A₁ ∈ modelsOf Θ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
        (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α' A₁ d})).Countable) ∧
      bfEquivSetoid L ℕ α A A₀ ∧ bfEquivSetoid L ℕ α A A₁ ∧ ¬ bfEquivSetoid L ℕ α' A₀ A₁ := by
  set K := modelsOf (V := ℕ) Θ
  -- the level class of `A` is a sentence cut of `K`, so some sentence `φ` splits it in two
  set C := K ∩ {d | bfEquivSetoid L ℕ α A d}
  have hC : C = modelsOf (V := ℕ) (Θ ⊓ A.scottSentenceAtLevel α) := by
    rw [modelsOf_inf, modelsOf_scottSentenceAtLevel A hα]
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (C ∩ modelsOf φ)).Countable ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) '' (C \ modelsOf φ)).Countable := by
    have h := hmin (A.scottSentenceAtLevel α)
    rw [minimallyUncountableOn_iff, ← hC] at h
    push Not at h
    exact h hlarge
  -- above the saturation level of `φ`, both sides contain a large level class
  obtain ⟨αφ, hαφ, hsatφ⟩ := exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) φ
  set α' := max (α + ω) αφ
  have hα' : α' < ω₁ :=
    max_lt (Ordinal.isPrincipal_add_omega 1 hα Ordinal.omega0_lt_omega_one) hαφ
  have hside (S : Set (RelationalConfiguration L ℕ)) (hSC : S ⊆ C)
      (hS : ¬ (Quotient.mk (isoSetoid L ℕ) '' S).Countable) : ∃ A' ∈ S, A' ∈ K ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (K ∩ {d | bfEquivSetoid L ℕ α' A' d})).Countable := by
    have := (hscat.mono (hSC.trans inter_subset_left)).countable_quotient hα'
    obtain ⟨A', hA', hlarge'⟩ := (bfEquivSetoid L ℕ α').exists_class_not_countable_image _ S hS
    refine ⟨A', hA', (hSC hA').1, fun h => hlarge' (h.mono (image_mono ?_))⟩
    exact inter_subset_inter_left _ (hSC.trans inter_subset_left)
  obtain ⟨A₀, hA₀, hP₀⟩ := hside _ inter_subset_left hφ₁
  obtain ⟨A₁, hA₁, hP₁⟩ := hside _ sdiff_subset hφ₂
  refine ⟨α', le_max_left _ _, hα', A₀, A₁, hP₀, hP₁, hA₀.1.2, hA₁.1.2, fun h01 => ?_⟩
  exact hA₁.2 ((hsatφ α' (le_max_right _ _) A₀ A₁ h01).1 hA₀.2)

/-- **The Harnik–Makkai reduction.** If the models on `ℕ` of a sentence `Θ` are back-and-forth
scattered and meet uncountably many isomorphism classes, then some strengthening `Θ ⊓ θ` has
minimally uncountable models on `ℕ`. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered [Countable (Σ n, L.Relations n)]
    {Θ : L.Sentenceω} (hscat : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  by_contra! hmin
  set K := modelsOf (V := ℕ) Θ
  obtain ⟨αΘ, hαΘ, hsatΘ⟩ := exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) Θ
  -- the nodes of the splitting tree: models of `Θ` at levels above the saturation level of `Θ`,
  -- whose level classes meet uncountably many isomorphism classes
  let P (A : RelationalConfiguration L ℕ) (α : Ordinal.{0}) : Prop := α < ω₁ ∧ αΘ ≤ α ∧ A ∈ K ∧
    ¬ (Quotient.mk (isoSetoid L ℕ) '' (K ∩ {d | bfEquivSetoid L ℕ α A d})).Countable
  have hroot : ∃ A α, P A α := by
    have := hscat.countable_quotient hαΘ
    obtain ⟨A, hA, hlarge⟩ := (bfEquivSetoid L ℕ αΘ).exists_class_not_countable_image _ K hunc
    exact ⟨A, αΘ, hαΘ, le_rfl, hA, hlarge⟩
  have hsplit (A : RelationalConfiguration L ℕ) (α : Ordinal.{0}) (hP : P A α) :
      ∃ α', α + ω ≤ α' ∧ ∃ A₀ A₁, P A₀ α' ∧ P A₁ α' ∧ bfEquivSetoid L ℕ α A A₀ ∧
        bfEquivSetoid L ℕ α A A₁ ∧ ¬ bfEquivSetoid L ℕ α' A₀ A₁ := by
    obtain ⟨α', hαα', hα', A₀, A₁, hP₀, hP₁, h₀, h₁, h01⟩ :=
      exists_bfClass_split hscat hmin hP.1 hP.2.2.2
    have hΘα' : αΘ ≤ α' := hP.2.1.trans (le_self_add.trans hαα')
    exact ⟨α', hαα', A₀, A₁, ⟨hα', hΘα', hP₀⟩, ⟨hα', hΘα', hP₁⟩, h₀, h₁, h01⟩
  obtain ⟨A, α, hP, hlvl, hchild, hsame, hne⟩ := exists_splitting_tree P hroot hsplit
  exact false_of_splitting_tree hscat A α (fun σ => (hP σ).1)
    (fun σ d hd => (hsatΘ _ (hP σ).2.1 _ _ hd).1 (hP σ).2.2.1) hlvl hchild hsame hne

/-- **Minimal counterexamples.** A sentence failing the perfect-set dichotomy for its countable
models has a strengthening whose models on `ℕ` are minimally uncountable. -/
theorem exists_minimallyUncountableOn_inf_of_not_hasVaughtDichotomy
    [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω} (h : ¬ HasVaughtDichotomy φ) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (φ ⊓ θ)) := by
  have h' := mt hasVaughtDichotomy_of_nat h
  push Not at h'
  refine exists_minimallyUncountableOn_inf_of_bfScattered
    (isThinOnNatModels_iff.2 h'.2).bfScattered_modelsOf ?_
  rw [← Setoid.countable_quotient_comap_val_iff]
  exact (uncountable_iff_not_countable _).1 h'.1

/-- **Vaught's conjecture from the absence of minimally uncountable sentences.** If no sentence
in a countable relational language in universe zero has minimally uncountable models on `ℕ`,
then Vaught's conjecture holds. -/
theorem vaughtConjecture_of_forall_not_minimallyUncountableOn
    (h : ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
      (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    VaughtConjecture := by
  rw [vaughtConjecture_iff]
  intro L _ _ φ
  by_contra hφ
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_inf_of_not_hasVaughtDichotomy hφ
  exact h L (φ ⊓ θ) hθ

end TauCeti
