/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.RelationalConfiguration.Separation
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
level on (`exists_bfLevel_saturated_modelsOf`, from uniform back-and-forth separation); and a
chain of codes equivalent at levels `α i + ω` has a limit code (`exists_limit_of_bfEquiv_chain`).
No continuum hypothesis and no continuity of the branch limits is used.

Consequently a counterexample to Vaught's conjecture has a strengthening with minimally
uncountable models, so Vaught's conjecture holds as soon as no sentence has minimally uncountable
models on `ℕ`.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes, and every
  sentence cut of `K` has a side meeting countably many.

## Main results

* `TauCeti.exists_bfLevel_saturated_modelsOf`: back-and-forth equivalence from some countable
  level on decides every sentence.
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
  §XII.2 (Theorem XII.7, whose splitting-tree proof is followed here, with the saturation of a
  sentence obtained from uniform back-and-forth separation instead of its quantifier complexity).
-/

public section

universe u v w uι o

open FirstOrder FirstOrder.Language Cardinal MeasureTheory Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Saturation of a sentence.** On a countable carrier, in a vocabulary with countably many
relation symbols of each arity, back-and-forth equivalence at every level from some countable
level `α` on decides each `L_{ω₁ω}` sentence. -/
theorem exists_bfLevel_saturated_modelsOf [∀ n, Countable (L.Relations n)] {V : Type w}
    [Countable V] {ι : Type uι} [Countable ι] (θ : L.SentenceInf ι) :
    ∃ α : Ordinal.{o}, α < ω₁ ∧ ∀ β ≥ α, ∀ c d : RelationalConfiguration L V,
      bfEquivSetoid L V β c d → (c ∈ modelsOf θ ↔ d ∈ modelsOf θ) := by
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_mem_iff_of_measurableSet (V := V) (C := univ)
    MeasurableSet.univ.analyticSet (measurableSet_modelsOf θ) fun c _ d _ hcd hc => by
      obtain ⟨e⟩ := isoSetoid_apply.mp hcd
      exact (e.mem_modelsOf_iff θ).mp hc
  exact ⟨α, hα, fun β hβ c d hcd => hsat β hβ c trivial d trivial hcd⟩

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

/-- A back-and-forth scattered, minimally uncountable set is concentrated at back-and-forth
levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (h : MinimallyUncountableOn K) (hK : BFScattered K) :
    ConcentratedAtBFLevels K :=
  concentratedAtBFLevels_of_bfScattered_of_sentence_splits hK h.2

/-- A set that is concentrated at back-and-forth levels and meets uncountably many isomorphism
classes is minimally uncountable: every sentence is saturated from some countable level on, so
one side of its cut lies off the centre's class. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : ConcentratedAtBFLevels K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) : MinimallyUncountableOn K := by
  refine ⟨hunc, fun θ => ?_⟩
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) θ
  have h := hK.countable_isoClasses_or_of_saturated inter_subset_left hα
    fun b hb c hc hbc => ⟨hc, (hsat α le_rfl b c hbc).1 hb.2⟩
  simpa only [Setoid.countable_quotient_comap_val_iff, sdiff_self_inter] using h

/-- A back-and-forth scattered set is minimally uncountable exactly when it is concentrated at
back-and-forth levels and meets uncountably many isomorphism classes. -/
theorem minimallyUncountableOn_iff_concentratedAtBFLevels [Countable (Σ n, L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable :=
  ⟨fun h => ⟨h.concentratedAtBFLevels hK, h.1⟩, fun h => h.1.minimallyUncountableOn h.2⟩

/-- A set meeting uncountably many isomorphism classes and countably many classes at level `α`
has a level-`α` class meeting it in uncountably many isomorphism classes. -/
private theorem exists_bfClass_not_countable_isoClasses {K : Set (RelationalConfiguration L ℕ)}
    (hK : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) {α : Ordinal.{0}}
    [Countable (Quotient ((bfEquivSetoid L ℕ α).comap (Subtype.val : K → _)))] :
    ∃ c ∈ K, ¬ (Quotient.mk (isoSetoid L ℕ) '' (K ∩ {d | bfEquivSetoid L ℕ α c d})).Countable := by
  refine (bfEquivSetoid L ℕ α).exists_class_not_small K
    (fun A => (Quotient.mk (isoSetoid L ℕ) '' A).Countable) (fun S hS hs => ?_) hK
  rw [image_sUnion, sUnion_image]
  exact hS.biUnion hs

/-- If each code of a sequence lies in the level-`α i` class of the previous one, and the levels
grow by at least `ω` at each step, some code lies in the level-`α i` class of every member. -/
private theorem exists_bfEquiv_of_chain {c : ℕ → RelationalConfiguration L ℕ}
    {α : ℕ → Ordinal.{0}} (hα : ∀ i, α i + ω ≤ α (i + 1))
    (hc : ∀ i, bfEquivSetoid L ℕ (α i) (c i) (c (i + 1))) :
    ∃ d, ∀ i, bfEquivSetoid L ℕ (α i) d (c i) := by
  obtain ⟨d, hd⟩ := exists_limit_of_bfEquiv_chain (c := fun i => c (i + 1))
    (monotone_nat_of_le_succ fun i => le_self_add.trans (hα i))
    fun i => bfEquivSetoid_anti (hα i) (hc (i + 1))
  exact ⟨d, fun i => (bfEquivSetoid L ℕ _).trans (hd i) ((bfEquivSetoid L ℕ _).symm (hc i))⟩

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
    fun n : Node => hsplit n.1.1 n.1.2 n.2
  let code (n : Node) (b : Bool) : RelationalConfiguration L ℕ := bif b then code₁ n else code₀ n
  have hcodeP (n : Node) (b : Bool) : P (code n b) (lvl n) := by cases b <;> simp [code, *]
  have hcode (n : Node) (b : Bool) : bfEquivSetoid L ℕ n.1.2 n.1.1 (code n b) := by
    cases b <;> simp [code, *]
  obtain ⟨A, α, hroot⟩ := hroot
  -- the node of a word `b :: σ` is the child `b` of the node of `σ`
  let node (σ : List Bool) : Node :=
    σ.foldr (fun b n => ⟨(code n b, lvl n), hcodeP n b⟩) ⟨(A, α), hroot⟩
  exact ⟨fun σ => (node σ).1.1, fun σ => (node σ).1.2, fun σ => (node σ).2,
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
  classical
  -- the branch through `X` passes through the reversed prefixes of `X`; choose its limit
  let word (X : ℕ → Bool) (i : ℕ) : List Bool := ((List.range i).reverse).map X
  have hword (X : ℕ → Bool) (i : ℕ) : word X (i + 1) = X i :: word X i := by
    simp [word, List.range_succ]
  choose d hd using fun X => exists_bfEquiv_of_chain (c := fun i => A (word X i))
    (α := fun i => α (word X i))
    (fun i => by simpa only [hword] using hlvl _ (X i))
    (fun i => by simpa only [hword] using hchild _ (X i))
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
    have hex : ∃ i, X i ≠ Y i := by
      by_contra! h
      exact hXY' (funext h)
    -- the branches pass through a common word `σ`, then through its two different children
    let i := Nat.find hex
    have hagree : word X i = word Y i :=
      List.map_congr_left fun j hj => by_contra fun h =>
        Nat.find_min hex (List.mem_range.1 (List.mem_reverse.1 hj)) h
    set σ := word X i
    have hlvlσ (b : Bool) : α (b :: σ) = α (true :: σ) := by cases b <;> simp [hsame]
    have hX : bfEquivSetoid L ℕ (α (true :: σ)) (d X) (A (X i :: σ)) := by
      have h := hd X (i + 1)
      rwa [hword, hlvlσ] at h
    have hY : bfEquivSetoid L ℕ (α (true :: σ)) (d Y) (A (Y i :: σ)) := by
      have h := hd Y (i + 1)
      rwa [hword, ← hagree, hlvlσ] at h
    have hXY := (bfEquivSetoid L ℕ _).trans ((bfEquivSetoid L ℕ _).symm hX)
      ((bfEquivSetoid L ℕ _).trans (bfEquivSetoid_anti (Ordinal.le_iSup α _) hXY) hY)
    have hXi : X i ≠ Y i := Nat.find_spec hex
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
    obtain ⟨A', hA', hlarge'⟩ := exists_bfClass_not_countable_isoClasses hS (α := α')
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
    obtain ⟨A, hA, hlarge⟩ := exists_bfClass_not_countable_isoClasses hunc (α := αΘ)
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
