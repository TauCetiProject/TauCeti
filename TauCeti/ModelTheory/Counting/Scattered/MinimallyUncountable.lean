/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Scattered.SentenceSplits
public import TauCeti.ModelTheory.Counting.Scattered.Vaught

/-!
# Minimally uncountable classes and the Harnik–Makkai reduction

A set `K` of relational configurations is *minimally uncountable* when it meets uncountably many
isomorphism classes, but every cut of `K` by an `L_{ω₁ω}` sentence has a side meeting only
countably many. Sentences with minimally uncountable models on `ℕ` are the minimal
counterexamples to Vaught's conjecture studied by Harnik and Makkai and by Steel.

The Harnik–Makkai reduction says that every sentence `Θ` whose models on `ℕ` are back-and-forth
scattered and meet uncountably many isomorphism classes has a minimally uncountable
strengthening `Θ ⊓ θ`. Suppose not. Call a set *large* when it meets uncountably many
isomorphism classes. Starting from a large level class inside the models of `Θ`, every large
level class `C` is the model class of `Θ` together with a Scott sentence at that level, so some
sentence `φ` cuts `C` into two large sides. Both sides are unions of back-and-forth classes from
the saturation level of `φ` on, and by scatteredness each side contains a large class at a
common level at least `ω` above the level of `C`. Iterating this split along every branch of the
binary tree, the limit of each branch is a model of `Θ`, and the limits of distinct branches are
inequivalent at the supremum of the countably many levels used. This produces continuum many
classes at one countable level, contradicting scatteredness. Neither continuity of the branch
limits nor the continuum hypothesis is used.

With the scattered reformulation of Vaught's conjecture, it follows that the conjecture holds
as soon as no sentence has minimally uncountable models on `ℕ`.

## Main definitions

* `TauCeti.MinimallyUncountableOn K`: `K` meets uncountably many isomorphism classes, and every
  sentence cut of `K` has a side meeting only countably many.

## Main results

* `TauCeti.exists_minimallyUncountableOn_inf_of_bfScattered`: the Harnik–Makkai reduction.
* `TauCeti.vaughtConjecture_of_forall_not_minimallyUncountableOn`: Vaught's conjecture holds if
  no sentence has minimally uncountable models on `ℕ`.

## References

* V. Harnik and M. Makkai, *A tree argument in infinitary model theory*, Proceedings of the
  American Mathematical Society 67 (1977), 309–314.
* J. R. Steel, *On Vaught's conjecture*, in *Cabal Seminar 76–77*, Lecture Notes in Mathematics
  689, Springer, 1978, 193–208.
* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Chapter XII,
  §XII.2 (Definition XII.4, Lemma XII.6 and Theorem XII.7). The splitting tree here is built in
  the one-element back-and-forth convention, with the limit of a back-and-forth chain in place of
  Lemma XII.6 and uniform back-and-forth separation in place of quantifier complexity.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language Cardinal Ordinal Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational]

/-- A set of configurations is *minimally uncountable* when it meets uncountably many
isomorphism classes, but every cut by an `L_{ω₁ω}` sentence has a side meeting only countably
many. -/
def MinimallyUncountableOn {V : Type w} (K : Set (RelationalConfiguration L V)) : Prop :=
  ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
    ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
      (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable

/-- Unfolding lemma for `TauCeti.MinimallyUncountableOn`. -/
theorem minimallyUncountableOn_iff {V : Type w} {K : Set (RelationalConfiguration L V)} :
    MinimallyUncountableOn K ↔ ¬ (Quotient.mk (isoSetoid L V) '' K).Countable ∧
      ∀ θ : L.Sentenceω, (Quotient.mk (isoSetoid L V) '' (K ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (K \ modelsOf θ)).Countable :=
  Iff.rfl

/-- **A splitting tree of back-and-forth classes refutes scatteredness.** Suppose every node
`(a, α)` satisfying `P` has a countable level `α` and splits into two members of `K` that are
`α`-equivalent to `a`, inequivalent at some level `α' ≥ α + ω`, and again nodes at level `α'`.
If some node lies at a level `α₀` from which on back-and-forth equivalence preserves membership
in `K`, then the limits of the branches of the tree lie in `K` and are pairwise inequivalent at
one countable level, so `K` is not scattered. -/
private theorem not_bfScattered_of_bfSplit {K : Set (RelationalConfiguration L ℕ)}
    {P : RelationalConfiguration L ℕ → Ordinal.{0} → Prop} (hlt : ∀ a α, P a α → α < ω₁)
    (hsplit : ∀ a α, P a α → ∃ α', α + ω ≤ α' ∧ ∃ b : Bool → RelationalConfiguration L ℕ,
      ¬ bfEquivSetoid L ℕ α' (b false) (b true) ∧
        ∀ i, b i ∈ K ∧ bfEquivSetoid L ℕ α a (b i) ∧ P (b i) α')
    {r : RelationalConfiguration L ℕ} {α₀ : Ordinal.{0}} (hr : P r α₀)
    (hsat : ∀ c d, bfEquivSetoid L ℕ α₀ c d → c ∈ K → d ∈ K) : ¬ BFScattered K := by
  intro hK
  let Q := {p : RelationalConfiguration L ℕ × Ordinal.{0} // P p.1 p.2}
  choose lvl hlvl_ge b hsep hb using fun p : Q => hsplit _ _ p.2
  let next (p : Q) (i : Bool) : Q := ⟨(b p i, lvl p), (hb p i).2.2⟩
  -- The node at a finite word, read with its most recent bit first.
  let node (w : List Bool) : Q := w.foldr (fun i p => next p i) ⟨(r, α₀), hr⟩
  -- The node reached along the first `n` bits of a branch `X`.
  let path (X : ℕ → Bool) (n : ℕ) : Q := node ((List.range n).reverse.map X)
  have path_succ (X : ℕ → Bool) (n : ℕ) : path X (n + 1) = next (path X n) (X n) := by
    simp only [path, node, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, List.foldr_cons]
  have path_congr {X Y : ℕ → Bool} {n : ℕ} (h : ∀ j < n, X j = Y j) : path X n = path Y n := by
    simp only [path]
    congr 1
    exact List.map_congr_left fun j hj => h j (by simpa using hj)
  -- Each branch is a back-and-forth chain with levels increasing by at least `ω`.
  have hlvl_le (X : ℕ → Bool) (n : ℕ) : (path X n).1.2 + ω ≤ (path X (n + 1)).1.2 := by
    rw [path_succ]
    exact hlvl_ge _
  have hlink (X : ℕ → Bool) (n : ℕ) :
      bfEquivSetoid L ℕ (path X n).1.2 (path X n).1.1 (path X (n + 1)).1.1 := by
    rw [path_succ]
    exact (hb _ _).2.1
  have hmono (X : ℕ → Bool) : Monotone fun n => (path X n).1.2 :=
    monotone_nat_of_le_succ fun n => le_self_add.trans (hlvl_le X n)
  choose d hd using fun X => exists_limit_of_bfEquiv_chain (hmono X) fun n =>
    bfEquivSetoid_anti (hlvl_le X n) (hlink X (n + 1))
  -- The limit of a branch is equivalent to each node of the branch at the level of that node.
  have hdnode (X : ℕ → Bool) (n : ℕ) :
      bfEquivSetoid L ℕ (path X (n + 1)).1.2 (d X) (path X (n + 1)).1.1 :=
    (bfEquivSetoid L ℕ _).trans (hd X (n + 1)) ((bfEquivSetoid L ℕ _).symm (hlink X (n + 1)))
  have hdK (X : ℕ → Bool) : d X ∈ K := by
    refine hsat _ _ ((bfEquivSetoid L ℕ _).symm (hd X 0)) ?_
    rw [path_succ]
    exact (hb _ _).1
  -- Distinct branches have inequivalent limits at the supremum of all node levels.
  have hβ : (⨆ w : List Bool, (node w).1.2) < ω₁ :=
    iSup_lt_omega_one fun w => hlt _ _ (node w).2
  have hinj : Function.Injective fun X => (Quotient.mk _ ⟨d X, hdK X⟩ :
      Quotient ((bfEquivSetoid L ℕ (⨆ w : List Bool, (node w).1.2)).comap
        (Subtype.val : K → _))) := by
    intro X Y hXY
    dsimp only at hXY
    by_contra hne
    have hex : ∃ n, X n ≠ Y n := by simpa only [Ne, funext_iff, not_forall] using hne
    classical
    set n := Nat.find hex
    have hpre : path X n = path Y n := path_congr fun j hj => not_not.1 (Nat.find_min hex hj)
    -- Both limits are equivalent, at the common level of the children of the node at `n`, to
    -- the children chosen by `X` and `Y`.
    have hX := hdnode X n
    have hY := hdnode Y n
    rw [path_succ, hpre] at hX
    rw [path_succ] at hY
    simp only [next] at hX hY
    have hlevel : (path Y (n + 1)).1.2 ≤ ⨆ w : List Bool, (node w).1.2 :=
      Ordinal.le_iSup (fun w : List Bool => (node w).1.2) ((List.range (n + 1)).reverse.map Y)
    rw [path_succ] at hlevel
    have hXY' : bfEquivSetoid L ℕ (⨆ w : List Bool, (node w).1.2) (d X) (d Y) :=
      Quotient.exact (s := (bfEquivSetoid L ℕ _).comap Subtype.val) hXY
    have h := (bfEquivSetoid L ℕ _).trans ((bfEquivSetoid L ℕ _).symm hX)
      ((bfEquivSetoid L ℕ _).trans (bfEquivSetoid_anti hlevel hXY') hY)
    have hspec : X n ≠ Y n := Nat.find_spec hex
    cases hXn : X n <;> cases hYn : Y n <;>
      simp only [hXn, hYn, ne_eq, not_true_eq_false] at h hspec
    · exact hsep _ h
    · exact hsep _ ((bfEquivSetoid L ℕ _).symm h)
  have hcard : #(ℕ → Bool) = 𝔠 := by simp
  have := hK.countable_quotient hβ
  have := hinj.countable
  exact aleph0_lt_continuum.not_ge (hcard ▸ mk_le_aleph0)

variable [Countable (Σ n, L.Relations n)] {Θ : L.Sentenceω}

/-- One splitting step of the Harnik–Makkai tree. If no strengthening of `Θ` has minimally
uncountable models and the level-`α` class of `a` meets the models of `Θ` in uncountably many
isomorphism classes, there are two models of `Θ`, both `α`-equivalent to `a`, inequivalent at a
countable level `α' ≥ α + ω`, whose level-`α'` classes again meet the models of `Θ` in
uncountably many isomorphism classes. -/
private theorem exists_bfSplit (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hmin : ∀ θ : L.Sentenceω, ¬ MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)))
    {a : RelationalConfiguration L ℕ} {α : Ordinal.{0}} (hα : α < ω₁)
    (ha : ¬ (Quotient.mk (isoSetoid L ℕ) ''
      (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α a d})).Countable) :
    ∃ α', α + ω ≤ α' ∧ ∃ b : Bool → RelationalConfiguration L ℕ,
      ¬ bfEquivSetoid L ℕ α' (b false) (b true) ∧ ∀ i, b i ∈ modelsOf Θ ∧
        bfEquivSetoid L ℕ α a (b i) ∧ α' < ω₁ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
          (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α' (b i) d})).Countable := by
  set N := modelsOf (V := ℕ) Θ ∩ {d | bfEquivSetoid L ℕ α a d}
  -- The level class `N` is a sentence cut, so some sentence `φ` splits it into two large sides.
  have hsplit := hmin (a.scottSentenceAtLevel α)
  rw [modelsOf_inf, modelsOf_scottSentenceAtLevel a hα, minimallyUncountableOn_iff, not_and,
    not_forall] at hsplit
  obtain ⟨φ, hφ⟩ := hsplit ha
  rw [not_or] at hφ
  obtain ⟨β, hβ, hsat⟩ := exists_bfLevel_mem_modelsOf_iff (V := ℕ) φ
  have hα' : max (α + ω) β < ω₁ :=
    max_lt (isPrincipal_add_omega 1 hα omega0_lt_omega_one) hβ
  -- Each large side contains a large class at level `max (α + ω) β`.
  have hside (S : Set (RelationalConfiguration L ℕ)) (hSN : S ⊆ N)
      (hS : ¬ (Quotient.mk (isoSetoid L ℕ) '' S).Countable) :
      ∃ c ∈ S, c ∈ modelsOf Θ ∧ bfEquivSetoid L ℕ α a c ∧ max (α + ω) β < ω₁ ∧
        ¬ (Quotient.mk (isoSetoid L ℕ) ''
          (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ (max (α + ω) β) c d})).Countable := by
    have := (hK.mono (hSN.trans inter_subset_left)).countable_quotient hα'
    obtain ⟨c, hc, hlarge⟩ := exists_bfClass_uncountable_isoClasses hS (α := max (α + ω) β)
    exact ⟨c, hc, (hSN hc).1, (hSN hc).2, hα', fun h => hlarge (h.mono (image_mono
      (inter_subset_inter_left _ (hSN.trans inter_subset_left))))⟩
  obtain ⟨b₀, hb₀φ, hb₀⟩ := hside (N ∩ modelsOf φ) inter_subset_left hφ.1
  obtain ⟨b₁, hb₁φ, hb₁⟩ := hside (N \ modelsOf φ) sdiff_subset hφ.2
  refine ⟨_, le_max_left _ _, fun i => cond i b₁ b₀, ?_, Bool.rec hb₀ hb₁⟩
  exact fun h => hb₁φ.2 ((hsat _ (le_max_right _ _) b₀ b₁ h).1 hb₀φ.2)

/-- **The Harnik–Makkai reduction.** If the models on `ℕ` of `Θ` are back-and-forth scattered and
meet uncountably many isomorphism classes, then some strengthening `Θ ⊓ θ` has minimally
uncountable models on `ℕ`. -/
theorem exists_minimallyUncountableOn_inf_of_bfScattered
    (hK : BFScattered (modelsOf (V := ℕ) Θ))
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' modelsOf (V := ℕ) Θ).Countable) :
    ∃ θ : L.Sentenceω, MinimallyUncountableOn (modelsOf (V := ℕ) (Θ ⊓ θ)) := by
  by_contra! hmin
  -- From a countable level `α₀` on, back-and-forth equivalence preserves the models of `Θ`.
  obtain ⟨α₀, hα₀, hsatΘ⟩ := exists_bfLevel_mem_modelsOf_iff (V := ℕ) Θ
  have := hK.countable_quotient hα₀
  obtain ⟨r, -, hr⟩ := exists_bfClass_uncountable_isoClasses hunc (α := α₀)
  -- Split large level classes of the models of `Θ` along a binary tree rooted at `r`.
  exact not_bfScattered_of_bfSplit
    (P := fun a α => α < ω₁ ∧ ¬ (Quotient.mk (isoSetoid L ℕ) ''
      (modelsOf Θ ∩ {d | bfEquivSetoid L ℕ α a d})).Countable)
    (fun _ _ h => h.1) (fun _ _ h => exists_bfSplit hK hmin h.1 h.2) ⟨hα₀, hr⟩
    (fun c d hcd => (hsatΘ α₀ le_rfl c d hcd).1) hK

/-- **Vaught's conjecture from the absence of minimally uncountable sentences.** If no sentence
in a countable relational language has minimally uncountable models on `ℕ`, then Vaught's
conjecture holds. -/
theorem vaughtConjecture_of_forall_not_minimallyUncountableOn
    (h : ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)]
      (φ : L.Sentenceω), ¬ MinimallyUncountableOn (modelsOf (V := ℕ) φ)) :
    VaughtConjecture := by
  refine vaughtConjecture_iff_bfScattered.2 fun L _ _ φ hscat => ?_
  by_contra hunc
  rw [isoSetoidOn, Setoid.countable_quotient_comap_val_iff] at hunc
  obtain ⟨θ, hθ⟩ := exists_minimallyUncountableOn_inf_of_bfScattered hscat hunc
  exact h L (φ ⊓ θ) hθ

end TauCeti
