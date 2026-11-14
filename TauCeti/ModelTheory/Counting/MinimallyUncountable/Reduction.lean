/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.MinimallyUncountable.Basic
public import TauCeti.ModelTheory.Counting.Scattered.Vaught
public import TauCeti.ModelTheory.RelationalConfiguration.Saturation

/-!
# The Harnik–Makkai reduction to minimally uncountable sentences

Every back-and-forth scattered class `K` of configurations on `ℕ` that meets uncountably many
isomorphism classes and is saturated at some countable back-and-forth level `α₀ < ω₁` contains an
entire countable back-and-forth class `{d | bfEquivSetoid L ℕ β c d}` (`β < ω₁`) that is minimally
uncountable (`TauCeti.BFScattered.exists_bfClass_subset_and_minimallyUncountableOn`).

The proof is the Harnik–Makkai / Steel splitting-tree construction:

1. **Root selection.** Since `K` is scattered, meets uncountably many isomorphism classes, and is
   saturated at `α₀ + ω < ω₁`, one `(α₀ + ω)`-class inside `K` still meets uncountably many
   isomorphism classes (`TauCeti.BFScattered.exists_bfClass_subset_and_uncountable_isoClasses`).
2. **Splitting step.** Suppose no countable back-and-forth class contained in `K` is minimally
   uncountable. Given `2ⁿ` `(αₙ + ω)`-classes `C σ ⊆ K` (`σ : Fin n → Bool`), each meeting
   uncountably many isomorphism classes, failure of minimal uncountability on each `C σ` produces an
   `L_{ω₁ω}` sentence `φ σ` splitting `C σ` into two pieces `C σ ∩ modelsOf (φ σ)` and
   `C σ \ modelsOf (φ σ)` that both meet uncountably many isomorphism classes. Uniform saturation
   (`TauCeti.RelationalConfiguration.exists_bfLevel_forall_saturated_modelsOf`) gives a single
   countable threshold `β₀ < ω₁` saturating all `2ⁿ` sentences `φ σ`. Setting
   `αₙ₊₁ = max (αₙ + ω) β₀`, both halves of each `C σ` are `(αₙ₊₁ + ω)`-saturated, so each contains
   an `(αₙ₊₁ + ω)`-class meeting uncountably many isomorphism classes.
3. **Chain limits.** Along each branch `X : ℕ → Bool`, consecutive chosen configurations are
   `(αₙ + ω)`-equivalent, so `TauCeti.RelationalConfiguration.exists_limit_of_bfEquiv_chain` builds
   a limit configuration `lim X ∈ K` that is `αₙ`-equivalent to the `n`-th node along `X`. Distinct
   branches `X ≠ Y` diverge at a first index `n`, disagree on `φ (X ↾ n)` via saturation at
   `αₙ₊₁`, and are therefore separated at `β = ⨆ m, αₘ < ω₁` — injecting Cantor space `ℕ → Bool`
   into the countable `β`-quotient of `K`.

Because below `ω₁` every back-and-forth class is defined by its Scott approximation sentence
(`TauCeti.RelationalConfiguration.modelsOf_scottSentenceAtLevel`), the minimally uncountable class
inside `K` is the model class of a single `L_{ω₁ω}` sentence
(`TauCeti.BFScattered.exists_minimallyUncountableOn_modelsOf_subset`). Specializing to
`K = modelsOf Θ` yields the Harnik–Makkai reduction
(`TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`): every back-and-forth scattered
(equivalently, thin) sentence with uncountably many models on `ℕ` up to isomorphism has a minimally
uncountable strengthening `Θ ⊓ θ`. Consequently Vaught's conjecture holds whenever no sentence is
both scattered (or thin) and minimally uncountable, and in particular whenever no sentence is
minimally uncountable (`TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`).

## Main results

* `TauCeti.BFScattered.exists_bfClass_subset_and_uncountable_isoClasses`: a scattered large set
  saturated at `β < ω₁` contains a full `β`-class meeting uncountably many isomorphism classes.
* `TauCeti.BFScattered.exists_bfClass_subset_and_minimallyUncountableOn` and
  `TauCeti.BFScattered.exists_minimallyUncountableOn_modelsOf_subset`: a scattered large set
  saturated at some countable level contains a minimally uncountable countable level class, hence a
  minimally uncountable `L_{ω₁ω}` model class.
* `TauCeti.exists_minimallyUncountableOn_modelsOf_subset_of_bfScattered`,
  `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`, and
  `TauCeti.IsThinOnNatModels.exists_minimallyUncountableOn_inf`: **the Harnik–Makkai reduction** for
  scattered and thin sentences.
* `TauCeti.vaughtConjecture_iff_forall_not_bfScattered_and_minimallyUncountableOn`,
  `TauCeti.vaughtConjecture_iff_forall_not_isThinOnNatModels_and_minimallyUncountableOn`, and
  `TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`: reductions of Vaught's conjecture
  to ruling out minimally uncountable sentences.

## References

* Victor Harnik and Michael Makkai, *A tree argument in infinitary model theory*, Proceedings of
  the American Mathematical Society 67 (1977), 309–314, Theorem 1.1.
* John R. Steel, *On Vaught's conjecture*, Cabal Seminar 76–77, Lecture Notes in Mathematics 689,
  Springer, 1978, 193–208.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the
  chapter on Vaught counterexamples.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Cambridge University
  Press, 2021, Part 2, Chapter XII, Lemma XII.11.
* Adapted from `exists_minimallyUncountableOn_and_of_bfScattered` in
  `InfinitaryLogic/Descriptive/MinimallyUncountable.lean` of Cameron Freer's
  `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a39bc3e0b`, Apache-2.0),
  generalized here to arbitrary countable-level-saturated scattered classes and arbitrary language
  universes.
-/

public section

universe u v uι

open FirstOrder FirstOrder.Language Ordinal Set

namespace TauCeti

open RelationalConfiguration

section SplittingTree

variable {L : Language.{u, v}} [L.IsRelational]

/-- If a back-and-forth scattered set `S` of configurations on `ℕ` meets uncountably many
isomorphism classes and is saturated at level `β < ω₁`, then `S` contains an entire `β`-class that
still meets uncountably many isomorphism classes. No countability hypothesis on `L` is needed. -/
theorem BFScattered.exists_bfClass_subset_and_uncountable_isoClasses
    {S : Set (RelationalConfiguration L ℕ)} (hS : BFScattered S)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' S).Countable)
    {β : Ordinal.{0}} (hβ : β < ω₁)
    (hsat : ∀ c ∈ S, ∀ d, bfEquivSetoid L ℕ β c d → d ∈ S) :
    ∃ c ∈ S, {d | bfEquivSetoid L ℕ β c d} ⊆ S ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ β c d}).Countable := by
  have := hS.countable_quotient hβ
  obtain ⟨c, hcS, hnot⟩ := (bfEquivSetoid L ℕ β).exists_class_not_small S
    (fun A => (Quotient.mk (isoSetoid L ℕ) '' A).Countable)
    (fun T hT hs => by
      rw [image_sUnion, sUnion_image]
      exact hT.biUnion hs)
    hunc
  have hsub : {d | bfEquivSetoid L ℕ β c d} ⊆ S := fun d hcd => hsat c hcS d hcd
  refine ⟨c, hcS, hsub, ?_⟩
  rwa [inter_eq_right.mpr hsub] at hnot

/-- Stage `n` of the Harnik–Makkai splitting tree inside `K`: a countable base ordinal `α < ω₁`
together with `2ⁿ` configurations whose `(α + ω)`-classes lie in `K` and each meet uncountably many
isomorphism classes. -/
private structure SplittingStage (K : Set (RelationalConfiguration L ℕ)) (n : ℕ) where
  α : Ordinal.{0}
  α_lt : α < ω₁
  node : (Fin n → Bool) → RelationalConfiguration L ℕ
  subset_K : ∀ σ, {d | bfEquivSetoid L ℕ (α + ω) (node σ) d} ⊆ K
  uncountable_class : ∀ σ,
    ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ (α + ω) (node σ) d}).Countable

/-- One transition in the Harnik–Makkai splitting tree from stage `n` to stage `n + 1`, recording
the splitting sentences `φ σ`, their saturation at `next.α`, the `(s.α + ω)`-step along each branch
extension, and agreement of each child node with the truth value chosen by its last bit. -/
private structure SplittingStep (K : Set (RelationalConfiguration L ℕ)) {n : ℕ}
    (s : SplittingStage K n) where
  next : SplittingStage K (n + 1)
  φ : (Fin n → Bool) → L.Sentenceω
  level_le : s.α + ω ≤ next.α
  step_equiv : ∀ τ : Fin (n + 1) → Bool,
    bfEquivSetoid L ℕ (s.α + ω) (s.node (Fin.init τ)) (next.node τ)
  sat_φ : ∀ σ c d, bfEquivSetoid L ℕ next.α c d →
    (c ∈ modelsOf (φ σ) ↔ d ∈ modelsOf (φ σ))
  node_mem_iff : ∀ τ : Fin (n + 1) → Bool,
    next.node τ ∈ modelsOf (φ (Fin.init τ)) ↔ τ (Fin.last n) = true

/-- On either side `b : Bool` of a sentence cut `φ` of a scattered `γ`-saturated class `C` whose
both sides meet uncountably many isomorphism classes, select a full `γ`-class inside that side. -/
private theorem exists_child_bfClass {C : Set (RelationalConfiguration L ℕ)} (hC : BFScattered C)
    {φ : L.Sentenceω}
    (hpos : ¬ (Quotient.mk (isoSetoid L ℕ) '' (C ∩ modelsOf φ)).Countable)
    (hneg : ¬ (Quotient.mk (isoSetoid L ℕ) '' (C \ modelsOf φ)).Countable)
    {γ : Ordinal.{0}} (hγ : γ < ω₁)
    (hsatC : ∀ x ∈ C, ∀ y, bfEquivSetoid L ℕ γ x y → y ∈ C)
    (hsatφ : ∀ x y, bfEquivSetoid L ℕ γ x y → (x ∈ modelsOf φ ↔ y ∈ modelsOf φ))
    (b : Bool) :
    ∃ c ∈ C, (c ∈ modelsOf φ ↔ b = true) ∧ {d | bfEquivSetoid L ℕ γ c d} ⊆ C ∧
      ¬ (Quotient.mk (isoSetoid L ℕ) '' {d | bfEquivSetoid L ℕ γ c d}).Countable := by
  let side : Set (RelationalConfiguration L ℕ) := if b then C ∩ modelsOf φ else C \ modelsOf φ
  have hsub : side ⊆ C := by cases b <;> simp [side, sdiff_subset]
  have hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' side).Countable := by
    cases b
    · exact hneg
    · exact hpos
  have hsat : ∀ x ∈ side, ∀ y, bfEquivSetoid L ℕ γ x y → y ∈ side := by
    intro x hx y hxy
    have hyC : y ∈ C := hsatC x (hsub hx) y hxy
    cases b
    · exact ⟨hyC, fun hyφ => hx.2 ((hsatφ x y hxy).mpr hyφ)⟩
    · exact ⟨hyC, (hsatφ x y hxy).mp hx.2⟩
  obtain ⟨c, hc_mem, hc_sub, hc_unc⟩ :=
    (hC.mono hsub).exists_bfClass_subset_and_uncountable_isoClasses hunc hγ hsat
  refine ⟨c, hsub hc_mem, ?_, hc_sub.trans hsub, hc_unc⟩
  cases b
  · simp only [side, Bool.false_eq_true, iff_false] at hc_mem ⊢
    exact hc_mem.2
  · simp only [side, iff_true] at hc_mem ⊢
    exact hc_mem.2

/-- Assuming no countable back-and-forth class inside the scattered set `K` is minimally
uncountable, every stage `s` of the splitting tree extends to a next stage. -/
private theorem nonempty_splittingStep [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K)
    (hno : ∀ c ∈ K, ∀ β : Ordinal.{0}, β < ω₁ →
      {d | bfEquivSetoid L ℕ β c d} ⊆ K → ¬ MinimallyUncountableOn {d | bfEquivSetoid L ℕ β c d})
    {n : ℕ} (s : SplittingStage K n) :
    Nonempty (SplittingStep K s) := by
  classical
  -- Split each `(s.α + ω)`-class `C σ` by a sentence `φ σ` with two large sides.
  have hαω : s.α + ω < ω₁ := Ordinal.isPrincipal_add_omega 1 s.α_lt Ordinal.omega0_lt_omega_one
  let C (σ : Fin n → Bool) : Set (RelationalConfiguration L ℕ) :=
    {d | bfEquivSetoid L ℕ (s.α + ω) (s.node σ) d}
  have hex_φ (σ : Fin n → Bool) : ∃ φ : L.Sentenceω,
      ¬ (Quotient.mk (isoSetoid L ℕ) '' (C σ ∩ modelsOf φ)).Countable ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) '' (C σ \ modelsOf φ)).Countable := by
    have hmemK : s.node σ ∈ K := s.subset_K σ ((bfEquivSetoid L ℕ (s.α + ω)).refl _)
    have hnot := hno (s.node σ) hmemK (s.α + ω) hαω (s.subset_K σ)
    rw [minimallyUncountableOn_iff, not_and, not_forall] at hnot
    obtain ⟨φ, hφ⟩ := hnot (s.uncountable_class σ)
    exact ⟨φ, not_or.mp hφ⟩
  choose φ hφ_pos hφ_neg using hex_φ
  -- Uniformly saturate all `2ⁿ` sentences `φ σ` at `α'`, and pick `(α' + ω)`-classes in both sides.
  obtain ⟨β₀, hβ₀, hsat_φ⟩ :=
    exists_bfLevel_forall_saturated_modelsOf.{u, v, 0, 0, 0} (V := ℕ) φ
  let α' : Ordinal.{0} := max (s.α + ω) β₀
  have hα'_lt : α' < ω₁ := max_lt hαω hβ₀
  have hα'ω_lt : α' + ω < ω₁ := Ordinal.isPrincipal_add_omega 1 hα'_lt Ordinal.omega0_lt_omega_one
  have hle₁ : s.α + ω ≤ α' := le_max_left _ _
  have hle₂ : β₀ ≤ α' := le_max_right _ _
  have hex_child (σ : Fin n → Bool) (b : Bool) :=
    exists_child_bfClass (hK.mono (s.subset_K σ)) (hφ_pos σ) (hφ_neg σ) hα'ω_lt
      (fun _ hx _ hxy =>
        (bfEquivSetoid L ℕ (s.α + ω)).trans' hx (bfEquivSetoid_anti (hle₁.trans le_self_add) hxy))
      (hsat_φ σ (α' + ω) (hle₂.trans le_self_add)) b
  choose child hchild_C hchild_iff hchild_sub hchild_unc using hex_child
  exact ⟨{
    next := {
      α := α'
      α_lt := hα'_lt
      node := fun τ => child (Fin.init τ) (τ (Fin.last n))
      subset_K := fun τ => (hchild_sub _ _).trans (s.subset_K (Fin.init τ))
      uncountable_class := fun τ => hchild_unc _ _ }
    φ := φ
    level_le := hle₁
    step_equiv := fun τ => hchild_C _ _
    sat_φ := fun σ c d hcd => hsat_φ σ α' hle₂ c d hcd
    node_mem_iff := fun τ => hchild_iff _ _ }⟩

/-- Restriction of an infinite branch `X : ℕ → Bool` to its first `n` coordinates. -/
private def prefixOf (X : ℕ → Bool) (n : ℕ) : Fin n → Bool :=
  fun i => X i.1

/-- Distinct branches `X ≠ Y` through a sequence of splitting steps produce limit configurations
separated at `⨆ m, (stage m).α`. -/
private theorem not_bfEquivSetoid_iSup_of_ne {K : Set (RelationalConfiguration L ℕ)}
    {stage : ∀ n, SplittingStage K n} (step : ∀ n, SplittingStep K (stage n))
    (hnext : ∀ n, (step n).next = stage (n + 1))
    {lim : (ℕ → Bool) → RelationalConfiguration L ℕ}
    (hlim : ∀ X n, bfEquivSetoid L ℕ (stage n).α (lim X) ((stage n).node (prefixOf X n)))
    {X Y : ℕ → Bool} (hXY : X ≠ Y) :
    ¬ bfEquivSetoid L ℕ (⨆ m, (stage m).α) (lim X) (lim Y) := by
  classical
  have hex_diff : ∃ n, X n ≠ Y n := Function.ne_iff.mp hXY
  let n := Nat.find hex_diff
  have hn_ne : X n ≠ Y n := Nat.find_spec hex_diff
  have hpref : prefixOf X n = prefixOf Y n := by
    funext i
    exact not_not.mp (Nat.find_min hex_diff i.2)
  have hlim' (Z : ℕ → Bool) :
      bfEquivSetoid L ℕ (step n).next.α (lim Z) ((step n).next.node (prefixOf Z (n + 1))) := by
    rw [hnext n]
    exact hlim Z (n + 1)
  have hX : lim X ∈ modelsOf ((step n).φ (prefixOf X n)) ↔ X n = true :=
    ((step n).sat_φ (prefixOf X n) (lim X) _ (hlim' X)).trans
      ((step n).node_mem_iff (prefixOf X (n + 1)))
  have hY : lim Y ∈ modelsOf ((step n).φ (prefixOf X n)) ↔ Y n = true := by
    rw [hpref]
    exact ((step n).sat_φ (prefixOf Y n) (lim Y) _ (hlim' Y)).trans
      ((step n).node_mem_iff (prefixOf Y (n + 1)))
  intro hβXY
  have hle : (step n).next.α ≤ ⨆ m, (stage m).α :=
    (hnext n).symm ▸ Ordinal.le_iSup (fun m => (stage m).α) (n + 1)
  have hiff := (step n).sat_φ (prefixOf X n) (lim X) (lim Y) (bfEquivSetoid_anti hle hβXY)
  exact hn_ne (Bool.eq_iff_iff.mpr ((hX.symm.trans hiff).trans hY))

/-- **The Harnik–Makkai tree theorem for scattered saturated classes.** In a countable relational
vocabulary, if `K` is a back-and-forth scattered set of configurations on `ℕ` that meets
uncountably many isomorphism classes and is saturated at some countable level `α₀ < ω₁`, then `K`
contains an entire countable back-and-forth class `{d | bfEquivSetoid L ℕ β c d}` (`β < ω₁`) that
is minimally uncountable. -/
theorem BFScattered.exists_bfClass_subset_and_minimallyUncountableOn
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L ℕ)}
    (hK : BFScattered K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsat₀ : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) :
    ∃ c ∈ K, ∃ β : Ordinal.{0}, β < ω₁ ∧
      {d | bfEquivSetoid L ℕ β c d} ⊆ K ∧
      MinimallyUncountableOn {d | bfEquivSetoid L ℕ β c d} := by
  classical
  by_contra! hno
  -- Build stage `0` from `α₀`-saturation of `K`, and iterate `nonempty_splittingStep`.
  have hα₀ω : α₀ + ω < ω₁ := Ordinal.isPrincipal_add_omega 1 hα₀ Ordinal.omega0_lt_omega_one
  obtain ⟨c₀, _, hc₀_sub, hc₀_unc⟩ := hK.exists_bfClass_subset_and_uncountable_isoClasses hunc hα₀ω
    fun c hc d hcd => hsat₀ c hc d (bfEquivSetoid_anti le_self_add hcd)
  let s₀ : SplittingStage K 0 := ⟨α₀, hα₀, fun _ => c₀, fun _ => hc₀_sub, fun _ => hc₀_unc⟩
  let stepOf : ∀ {n : ℕ} (s : SplittingStage K n), SplittingStep K s :=
    fun s => Classical.choice (nonempty_splittingStep hK hno s)
  let stage : ∀ n : ℕ, SplittingStage K n := Nat.rec s₀ fun _ s => (stepOf s).next
  -- Along each branch `X : ℕ → Bool`, take a limit configuration `lim X ∈ K`.
  have hmono : Monotone fun n => (stage n).α :=
    monotone_nat_of_le_succ fun n => le_self_add.trans (stepOf (stage n)).level_le
  have hex_lim (X : ℕ → Bool) :
      ∃ d, ∀ n, bfEquivSetoid L ℕ (stage n).α d ((stage n).node (prefixOf X n)) :=
    exists_limit_of_bfEquiv_chain hmono fun n => (stepOf (stage n)).step_equiv (prefixOf X (n + 1))
  choose lim hlim using hex_lim
  have hmemK (X : ℕ → Bool) : lim X ∈ K := by
    have h1 : bfEquivSetoid L ℕ ((stage 0).α + ω) (lim X) ((stage 1).node (prefixOf X 1)) :=
      bfEquivSetoid_anti (stepOf (stage 0)).level_le (hlim X 1)
    have h01 := (stepOf (stage 0)).step_equiv (prefixOf X 1)
    exact (stage 0).subset_K (prefixOf X 0)
      ((bfEquivSetoid L ℕ ((stage 0).α + ω)).trans' h01
        ((bfEquivSetoid L ℕ ((stage 0).α + ω)).symm' h1))
  -- Inject `ℕ → Bool` into the countable `(⨆ m, (stage m).α)`-quotient of `K`.
  let β : Ordinal.{0} := ⨆ m, (stage m).α
  have := hK.countable_quotient (Ordinal.iSup_lt_omega_one fun m => (stage m).α_lt : β < ω₁)
  have hinj : Function.Injective
      (fun X : ℕ → Bool => (⟦⟨lim X, hmemK X⟩⟧ :
        Quotient ((bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)))) := by
    intro X Y hq
    by_contra hXY
    exact not_bfEquivSetoid_iSup_of_ne (fun n => stepOf (stage n)) (fun _ => rfl) hlim hXY
      (Quotient.exact (s := (bfEquivSetoid L ℕ β).comap (Subtype.val : K → _)) hq)
  have : Countable (ℕ → Bool) := hinj.countable
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ → Bool)
  exact Function.cantor_surjective (fun k => {m | e k m = true}) fun S => by
    obtain ⟨k, hk⟩ := he fun m => decide (m ∈ S)
    exact ⟨k, Set.ext fun m => (congrArg (· = true) (congrFun hk m)).to_iff.trans
      decide_eq_true_iff⟩

/-- Every scattered set `K` of configurations on `ℕ` meeting uncountably many isomorphism classes
and saturated at some countable level `α₀ < ω₁` contains the model class of a single `L_{ω₁ω}`
sentence `θ` that is minimally uncountable. -/
theorem BFScattered.exists_minimallyUncountableOn_modelsOf_subset
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L ℕ)}
    (hK : BFScattered K) (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable)
    {α₀ : Ordinal.{0}} (hα₀ : α₀ < ω₁)
    (hsat₀ : ∀ c ∈ K, ∀ d, bfEquivSetoid L ℕ α₀ c d → d ∈ K) :
    ∃ θ : L.Sentenceω, modelsOf (V := ℕ) θ ⊆ K ∧ MinimallyUncountableOn (modelsOf (V := ℕ) θ) := by
  obtain ⟨c, _, β, hβ, hsub, hmin⟩ :=
    hK.exists_bfClass_subset_and_minimallyUncountableOn hunc hα₀ hsat₀
  refine ⟨c.scottSentenceAtLevel β, ?_, ?_⟩ <;> rwa [modelsOf_scottSentenceAtLevel c hβ]

end SplittingTree

/-! ### Sentence forms and Vaught's conjecture -/

section Sentences

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- For any infinitary sentence `Θ` with countable branching whose models on `ℕ` are back-and-forth
scattered and uncountable up to isomorphism, some `L_{ω₁ω}` sentence `θ` has
`modelsOf (V := ℕ) θ ⊆ modelsOf (V := ℕ) Θ` and `MinimallyUncountableOn (modelsOf (V := ℕ) θ)`. -/
theorem exists_minimallyUncountableOn_modelsOf_subset_of_bfScattered
    {ι : Type uι} [Countable ι] {Θ : L.SentenceInf ι}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, modelsOf (V := ℕ) θ ⊆ modelsOf (V := ℕ) Θ ∧
      MinimallyUncountableOn (modelsOf (V := ℕ) θ) := by
  obtain ⟨α₀, hα₀, hsat₀⟩ := exists_bfLevel_saturated_modelsOf.{u, v, 0, uι, 0} (V := ℕ) Θ
  exact hK.exists_minimallyUncountableOn_modelsOf_subset hunc hα₀
    fun c hc d hcd => (hsat₀ α₀ le_rfl c d hcd).mp hc

/-- **The Harnik–Makkai reduction.** In a countable relational vocabulary, every `L_{ω₁ω}` sentence
`Θ` whose models on `ℕ` are back-and-forth scattered and meet uncountably many isomorphism classes
admits an `L_{ω₁ω}` strengthening `Θ ⊓ θ` whose model class on `ℕ` is minimally uncountable. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered {Θ : L.Sentenceω}
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  obtain ⟨θ, hsub, hmin⟩ := exists_minimallyUncountableOn_modelsOf_subset_of_bfScattered hK hunc
  refine ⟨θ, ?_⟩
  rwa [modelsOf_inf, inter_eq_right.mpr hsub]

/-- Thin-sentence form of `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`. -/
theorem IsThinOnNatModels.exists_minimallyUncountableOn_inf {Θ : L.Sentenceω}
    (hthin : IsThinOnNatModels Θ) (hunc : ¬ Countable (Quotient (isoSetoidOn ℕ Θ))) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) :=
  exists_minimallyUncountableOn_inf_of_bfScattered hthin.bfScattered_modelsOf
    (Setoid.countable_quotient_comap_val_iff.not.mp hunc)

end Sentences

/-- Any sentence in universe zero whose model class on `ℕ` is back-and-forth scattered and
minimally uncountable refutes Vaught's conjecture. -/
theorem not_vaughtConjecture_of_bfScattered_of_minimallyUncountableOn
    {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)] {φ : L.Sentenceω}
    (hscat : BFScattered (modelsOf (V := ℕ) φ))
    (hmin : MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    ¬ VaughtConjecture :=
  fun hv => hmin.not_countable_quotient (vaughtConjecture_iff_bfScattered.mp hv L φ hscat)

/-- **Scattered minimally uncountable reduction of Vaught's conjecture.** Vaught's conjecture holds
if and only if no `L_{ω₁ω}` sentence has a model class on `ℕ` that is both back-and-forth scattered
and minimally uncountable. -/
theorem vaughtConjecture_iff_forall_not_bfScattered_and_minimallyUncountableOn :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω),
        ¬ (BFScattered (modelsOf (V := ℕ) φ) ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) := by
  constructor
  · rintro hv L _ _ φ ⟨hscat, hmin⟩
    exact not_vaughtConjecture_of_bfScattered_of_minimallyUncountableOn hscat hmin hv
  · intro h
    refine vaughtConjecture_iff_bfScattered.mpr fun L _ _ φ hscat => ?_
    by_contra hunc
    have hunc' : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) φ).Countable :=
      Setoid.countable_quotient_comap_val_iff.not.mp hunc
    obtain ⟨θ, hmin⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc'
    have hscat' : BFScattered (modelsOf (V := ℕ) (φ ⊓ θ)) :=
      hscat.mono (modelsOf_inf φ θ ▸ inter_subset_left)
    exact h L (φ ⊓ θ) ⟨hscat', hmin⟩

/-- **Thin minimally uncountable reduction of Vaught's conjecture.** Vaught's conjecture holds if
and only if no `L_{ω₁ω}` sentence is both thin on `ℕ` and minimally uncountable on `ℕ`. -/
theorem vaughtConjecture_iff_forall_not_isThinOnNatModels_and_minimallyUncountableOn :
    VaughtConjecture ↔
      ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
        (φ : L.Sentenceω),
        ¬ (IsThinOnNatModels φ ∧ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) := by
  rw [vaughtConjecture_iff_forall_not_bfScattered_and_minimallyUncountableOn]
  refine forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun φ => not_congr (and_congr_left' ?_)
  exact bfScattered_modelsOf_iff_isThinOnNatModels

/-- **Vaught's conjecture from ruling out minimally uncountable sentences.** If no `L_{ω₁ω}`
sentence has a minimally uncountable model class on `ℕ`, then Vaught's conjecture holds. -/
theorem vaughtConjecture_of_forall_not_minimallyUncountableOn
    (h : ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
      (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    VaughtConjecture :=
  vaughtConjecture_iff_forall_not_bfScattered_and_minimallyUncountableOn.mpr
    fun L _ _ φ ⟨_, hmin⟩ => h L φ hmin

end TauCeti
