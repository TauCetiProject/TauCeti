/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.StdSimplex

/-!
# Sequence forms of strategies in tree-form decision processes

A tree-form sequential decision process has finitely many decision points `j : J`, each with
finitely many actions `A j`. Each decision point is reached through a *sequence*, the last
decision point and action that lead to it, given by a map `parent : J → Option (Σ j, A j)`, where
`none` is the empty sequence at the start of the process. Several decision points may share a
parent; between them the process makes an observation. A rank `ρ : J → ℕ` that increases from
each decision point to the decision points following it makes the process a forest.

A strategy of the player is recorded by its *sequence form* `x : Option (Σ j, A j) → ℝ`, the
probability with which the player plays all the actions of each sequence. This turns the
player's expected utility into a linear function of the strategy.

* `TauCeti.sequenceFormPolytope parent`: the sequence-form polytope, the vectors `x` with
  `x none = 1`, `x ≥ 0` and `∑ a, x (some ⟨j, a⟩) = x (parent j)` for each decision point `j`.
* `TauCeti.IsSequenceForm parent b x`: `x` is the sequence form of the weights `b`, that is,
  `x none = 1` and `x (some ⟨j, a⟩) = x (parent j) * b j a`.
* `TauCeti.IsBestResponseValue parent ℓ W`: `W` satisfies the recursion computing the best value
  of the linear utility `ℓ` from each sequence onwards, from the leaves up.

## Main results

* `TauCeti.exists_isSequenceForm`, `TauCeti.IsSequenceForm.unique`: every family of weights has
  a unique sequence form.
* `TauCeti.mem_sequenceFormPolytope_iff`: Kuhn's theorem in sequence form. The points of the
  sequence-form polytope are exactly the sequence forms of the behavioral strategies, the
  families of weights `b` with each `b j` in the probability simplex.
* `TauCeti.sequenceFormPolytope_subset_Icc`, `TauCeti.isCompact_sequenceFormPolytope`,
  `TauCeti.convex_sequenceFormPolytope`, `TauCeti.sequenceFormPolytope_nonempty`: the polytope
  is a nonempty compact convex subset of `[0, 1]^(sequences)`.
* `TauCeti.exists_isBestResponseValue`: the best-response values exist for every utility.
* `TauCeti.isGreatest_linear_bestResponse`: the maximum of the linear function
  `x ↦ ∑ s, ℓ s * x s` over the sequence-form polytope is `ℓ none` plus the sum, over the first
  decision points, of their best values; it is attained at the sequence form of a pure strategy
  playing a best action at every decision point
  (`TauCeti.IsSequenceForm.sum_mul_eq_of_isBestResponseValue`).

## References

* D. Koller, N. Megiddo and B. von Stengel, *Fast algorithms for finding randomized strategies
  in game trees*, STOC 1994, 750–759, Lemma 5.1.
* B. von Stengel, *Efficient computation of behavior strategies*, Games Econom. Behav. **14**
  (1996), 220–246, Definition 3.3 and Proposition 3.4 for realization plans and Corollary 4.2
  for Kuhn's theorem.
-/

public section

open Finset Convexity

namespace TauCeti

variable {J : Type*} {A : J → Type*}

/-! ### The sequence-form polytope and sequence forms -/

section Polytope

variable [∀ j, Fintype (A j)]

/-- The sequence-form polytope of the decision process with parent map `parent`: the vectors
indexed by sequences that are `1` at the empty sequence, nonnegative, and such that at each
decision point `j` the values at the sequences `⟨j, a⟩` add up to the value at the sequence
`parent j` leading to `j`. -/
def sequenceFormPolytope (parent : J → Option (Σ j, A j)) : Set (Option (Σ j, A j) → ℝ) :=
  {x | x none = 1 ∧ (∀ s, 0 ≤ x s) ∧ ∀ j, ∑ a, x (some ⟨j, a⟩) = x (parent j)}

/-- Membership in the sequence-form polytope, unfolded. -/
@[simp]
theorem mem_sequenceFormPolytope {parent : J → Option (Σ j, A j)}
    {x : Option (Σ j, A j) → ℝ} :
    x ∈ sequenceFormPolytope parent ↔
      x none = 1 ∧ (∀ s, 0 ≤ x s) ∧ ∀ j, ∑ a, x (some ⟨j, a⟩) = x (parent j) :=
  Iff.rfl

end Polytope

/-- `x` is the sequence form of the weights `b : ∀ j, A j → ℝ`: it is `1` at the empty sequence,
and its value at the sequence `⟨j, a⟩` is its value at the sequence `parent j` leading to `j`
times the weight `b j a`. For a behavioral strategy `b`, `x s` is the probability that the
player plays all the actions of the sequence `s`. -/
structure IsSequenceForm (parent : J → Option (Σ j, A j)) (b : ∀ j, A j → ℝ)
    (x : Option (Σ j, A j) → ℝ) : Prop where
  /-- The sequence form is `1` at the empty sequence. -/
  apply_none : x none = 1
  /-- The value at `⟨j, a⟩` is the value at `parent j` times the weight of `a` at `j`. -/
  apply_some (j : J) (a : A j) : x (some ⟨j, a⟩) = x (parent j) * b j a

section Rank

variable {parent : J → Option (Σ j, A j)} {ρ : J → ℕ}

/-- Induction over the sequences of a decision process whose rank increases from each decision
point to the decision points following it: a property of sequences that holds at the empty
sequence, and holds at each sequence `⟨j, a⟩` as soon as it holds at the sequence `parent j`
leading to `j`, holds at every sequence. -/
@[elab_as_elim]
theorem sequence_induction (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j)
    {P : Option (Σ j, A j) → Prop} (empty : P none)
    (step : ∀ j a, P (parent j) → P (some ⟨j, a⟩)) (s : Option (Σ j, A j)) : P s := by
  have hparent (j : J) : P (parent j) := by
    induction j using (InvImage.wf ρ wellFounded_lt).induction with
    | _ j ih =>
      match h : parent j with
      | none => exact empty
      | some ⟨j', a⟩ => exact step j' a (ih j' (hρ j j' a h))
  rcases s with _ | ⟨j, a⟩
  exacts [empty, step j a (hparent j)]

/-- Every family of weights has a sequence form. -/
theorem exists_isSequenceForm (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j)
    (b : ∀ j, A j → ℝ) : ∃ x, IsSequenceForm parent b x := by
  -- `y j` is the value of the sequence form at the sequence `parent j` leading to `j`.
  let F : ∀ j : J, (∀ j' : J, InvImage (· < ·) ρ j' j → ℝ) → ℝ := fun j ih ↦
    match h : parent j with
    | none => 1
    | some s => ih s.1 (hρ j s.1 s.2 h) * b s.1 s.2
  let y : J → ℝ := (InvImage.wf ρ wellFounded_lt).fix F
  have hy (j : J) : y j = (parent j).elim 1 fun s ↦ y s.1 * b s.1 s.2 := by
    simp only [y]
    rw [WellFounded.fix_eq]
    simp only [F]
    split <;> simp_all
  refine ⟨fun s ↦ s.elim 1 fun s ↦ y s.1 * b s.1 s.2, rfl, fun j a ↦ ?_⟩
  simp [← hy]

/-- The sequence form of a family of weights is unique. -/
theorem IsSequenceForm.unique (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j)
    {b : ∀ j, A j → ℝ} {x y : Option (Σ j, A j) → ℝ} (hx : IsSequenceForm parent b x)
    (hy : IsSequenceForm parent b y) : x = y :=
  funext fun s ↦ sequence_induction hρ (by rw [hx.apply_none, hy.apply_none])
    (fun j a h ↦ by rw [hx.apply_some, hy.apply_some, h]) s

/-- The sequence form of nonnegative weights is nonnegative. -/
theorem IsSequenceForm.nonneg (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j)
    {b : ∀ j, A j → ℝ} {x : Option (Σ j, A j) → ℝ} (hx : IsSequenceForm parent b x)
    (hb : ∀ j a, 0 ≤ b j a) (s : Option (Σ j, A j)) : 0 ≤ x s :=
  sequence_induction hρ (by rw [hx.apply_none]; exact zero_le_one)
    (fun j a h ↦ by rw [hx.apply_some]; exact mul_nonneg h (hb j a)) s

variable [∀ j, Fintype (A j)]

/-- The sequence form of a behavioral strategy lies in the sequence-form polytope. -/
theorem IsSequenceForm.mem_sequenceFormPolytope
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) {b : ∀ j, A j → ℝ}
    {x : Option (Σ j, A j) → ℝ} (hx : IsSequenceForm parent b x)
    (hb : ∀ j, b j ∈ Set.range fun p : StdSimplex ℝ (A j) ↦ ⇑p.weights) :
    x ∈ sequenceFormPolytope parent := by
  have hb' j := StdSimplex.mem_range_toFun_comp_weights_iff.1 (hb j)
  refine ⟨hx.apply_none, hx.nonneg hρ fun j ↦ (hb' j).1, fun j ↦ ?_⟩
  simp_rw [hx.apply_some, ← mul_sum, (hb' j).2, mul_one]

/-- Every point of the sequence-form polytope is the sequence form of some behavioral
strategy. -/
theorem exists_isSequenceForm_of_mem_sequenceFormPolytope [∀ j, Nonempty (A j)]
    {x : Option (Σ j, A j) → ℝ} (hx : x ∈ sequenceFormPolytope parent) :
    ∃ b : ∀ j, A j → ℝ, (∀ j, b j ∈ Set.range fun p : StdSimplex ℝ (A j) ↦ ⇑p.weights) ∧
      IsSequenceForm parent b x := by
  classical
  obtain ⟨hx1, hx0, hxsum⟩ := hx
  -- At a decision point `j` with `0 < x (parent j)`, play `a` with probability
  -- `x (some ⟨j, a⟩) / x (parent j)`; elsewhere, play a fixed point mass `c j`.
  let c (j : J) : A j → ℝ :=
    ⇑(StdSimplex.single (Classical.arbitrary (A j)) : StdSimplex ℝ _).weights
  refine ⟨fun j ↦ if 0 < x (parent j) then fun a ↦ x (some ⟨j, a⟩) / x (parent j) else c j,
    fun j ↦ ?_, hx1, fun j a ↦ ?_⟩
  · dsimp only
    split_ifs with hj
    · refine StdSimplex.mem_range_toFun_comp_weights_iff.2
        ⟨fun a ↦ div_nonneg (hx0 _) hj.le, ?_⟩
      rw [← sum_div, hxsum, div_self hj.ne']
    · exact ⟨_, rfl⟩
  · split_ifs with hj
    · rw [mul_div_cancel₀ _ hj.ne']
    · have hj0 : x (parent j) = 0 := le_antisymm (not_lt.1 hj) (hx0 _)
      rw [hj0, zero_mul]
      exact (sum_eq_zero_iff_of_nonneg fun a _ ↦ hx0 _).1 ((hxsum j).trans hj0) a (mem_univ a)

/-- **Kuhn's theorem in sequence form**: the points of the sequence-form polytope are exactly
the sequence forms of the behavioral strategies. -/
theorem mem_sequenceFormPolytope_iff [∀ j, Nonempty (A j)]
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) {x : Option (Σ j, A j) → ℝ} :
    x ∈ sequenceFormPolytope parent ↔
      ∃ b : ∀ j, A j → ℝ, (∀ j, b j ∈ Set.range fun p : StdSimplex ℝ (A j) ↦ ⇑p.weights) ∧
        IsSequenceForm parent b x :=
  ⟨exists_isSequenceForm_of_mem_sequenceFormPolytope, fun ⟨_, hb, hx⟩ ↦
    hx.mem_sequenceFormPolytope hρ hb⟩

/-- The values of a point of the sequence-form polytope lie in `[0, 1]`. -/
theorem sequenceFormPolytope_subset_Icc
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) :
    sequenceFormPolytope parent ⊆ Set.Icc 0 1 := by
  rintro x ⟨hx1, hx0, hxsum⟩
  refine ⟨hx0, fun s ↦ sequence_induction hρ hx1.le (fun j a h ↦ ?_) s⟩
  calc x (some ⟨j, a⟩) ≤ ∑ a', x (some ⟨j, a'⟩) :=
        single_le_sum (f := fun a' ↦ x (some ⟨j, a'⟩)) (fun a' _ ↦ hx0 _) (mem_univ a)
    _ = x (parent j) := hxsum j
    _ ≤ 1 := h

variable (parent) in
/-- The sequence-form polytope is closed. -/
theorem isClosed_sequenceFormPolytope : IsClosed (sequenceFormPolytope parent) := by
  have h1 : IsClosed {x : Option (Σ j, A j) → ℝ | x none = 1} :=
    isClosed_eq (continuous_apply _) continuous_const
  have h2 : IsClosed {x : Option (Σ j, A j) → ℝ | ∀ s, 0 ≤ x s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s ↦ isClosed_le continuous_const (continuous_apply s)
  have h3 : IsClosed
      {x : Option (Σ j, A j) → ℝ | ∀ j, ∑ a, x (some ⟨j, a⟩) = x (parent j)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j ↦ isClosed_eq
      (continuous_finsetSum _ fun a _ ↦ continuous_apply _) (continuous_apply _)
  exact h1.inter (h2.inter h3)

/-- The sequence-form polytope is compact. -/
theorem isCompact_sequenceFormPolytope
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) :
    IsCompact (sequenceFormPolytope parent) :=
  isCompact_Icc.of_isClosed_subset (isClosed_sequenceFormPolytope parent)
    (sequenceFormPolytope_subset_Icc hρ)

variable (parent) in
/-- The sequence-form polytope is convex. -/
theorem convex_sequenceFormPolytope : Convex ℝ (sequenceFormPolytope parent) := by
  rintro x ⟨hx1, hx0, hxsum⟩ y ⟨hy1, hy0, hysum⟩ s t hs ht hst
  refine ⟨by simp [hx1, hy1, hst], fun u ↦ ?_, fun j ↦ ?_⟩
  · simpa using add_nonneg (mul_nonneg hs (hx0 u)) (mul_nonneg ht (hy0 u))
  · simp [sum_add_distrib, ← mul_sum, hxsum, hysum]

/-- The sequence-form polytope is nonempty. -/
theorem sequenceFormPolytope_nonempty [∀ j, Nonempty (A j)]
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) :
    (sequenceFormPolytope parent).Nonempty := by
  obtain ⟨x, hx⟩ := exists_isSequenceForm hρ fun j ↦
    ⇑(StdSimplex.single (Classical.arbitrary (A j)) : StdSimplex ℝ _).weights
  exact ⟨x, hx.mem_sequenceFormPolytope hρ fun j ↦ ⟨_, rfl⟩⟩

end Rank

/-! ### Best responses -/

section BestResponse

variable [Fintype J] [DecidableEq J] [∀ j, DecidableEq (A j)]
  {parent : J → Option (Σ j, A j)} {ρ : J → ℕ}

/-- `W` satisfies the best-response recursion for the utility vector `ℓ`: the value `W ⟨j, a⟩` of
the sequence `⟨j, a⟩` is its utility plus, for each decision point `j'` that it leads to, the best
value `⨆ a', W ⟨j', a'⟩` of the sequences at `j'`. -/
def IsBestResponseValue (parent : J → Option (Σ j, A j)) (ℓ : Option (Σ j, A j) → ℝ)
    (W : (Σ j, A j) → ℝ) : Prop :=
  ∀ s : Σ j, A j, W s = ℓ (some s) + ∑ j' with parent j' = some s, ⨆ a', W ⟨j', a'⟩

theorem isBestResponseValue_iff {ℓ : Option (Σ j, A j) → ℝ} {W : (Σ j, A j) → ℝ} :
    IsBestResponseValue parent ℓ W ↔
      ∀ s : Σ j, A j, W s = ℓ (some s) + ∑ j' with parent j' = some s, ⨆ a', W ⟨j', a'⟩ :=
  Iff.rfl

/-- The best-response values exist for every utility vector. -/
theorem exists_isBestResponseValue (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j)
    (ℓ : Option (Σ j, A j) → ℝ) : ∃ W, IsBestResponseValue parent ℓ W := by
  -- The recursion goes up the rank, which is bounded by `N`.
  let N := univ.sup ρ + 1
  have hlt {j j' : J} {a : A j} (h : parent j' = some ⟨j, a⟩) : N - ρ j' < N - ρ j := by
    have := hρ j' j a h
    have : ρ j' ≤ univ.sup ρ := le_sup (mem_univ j')
    omega
  let F : ∀ j : J, (∀ j' : J, InvImage (· < ·) (fun j ↦ N - ρ j) j' j → A j' → ℝ) → A j → ℝ :=
    fun j ih a ↦ ℓ (some ⟨j, a⟩) +
      ∑ j', if h : parent j' = some ⟨j, a⟩ then ⨆ a', ih j' (hlt h) a' else 0
  let V := (InvImage.wf (fun j ↦ N - ρ j) wellFounded_lt).fix F
  refine ⟨fun s ↦ V s.1 s.2, fun ⟨j, a⟩ ↦ ?_⟩
  simp only [V]
  rw [WellFounded.fix_eq]
  simp [F, sum_filter]

variable [∀ j, Fintype (A j)]

/-- The utility of `x` and the best values of the decision points weighted by `x` at their
parents: the identity behind the best-response theorem, valid for every vector `x`. -/
private theorem sum_mul_add_sum_eq {ℓ : Option (Σ j, A j) → ℝ} {W : (Σ j, A j) → ℝ}
    (hW : IsBestResponseValue parent ℓ W) (x : Option (Σ j, A j) → ℝ) :
    ∑ s, ℓ s * x s + ∑ j, (⨆ a, W ⟨j, a⟩) * x (parent j) =
      (ℓ none + ∑ j with parent j = none, ⨆ a, W ⟨j, a⟩) * x none +
        ∑ s : Σ j, A j, W s * x (some s) := by
  have hfib : ∑ j, (⨆ a, W ⟨j, a⟩) * x (parent j) =
      ∑ s, x s * ∑ j with parent j = s, ⨆ a, W ⟨j, a⟩ := by
    rw [← sum_fiberwise univ parent]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun j hj ↦ by rw [(mem_filter.1 hj).2, mul_comm]
  have hW' (s : Σ j, A j) : W s * x (some s) =
      ℓ (some s) * x (some s) + x (some s) * ∑ j with parent j = some s, ⨆ a, W ⟨j, a⟩ := by
    rw [hW s]
    ring
  rw [hfib, Fintype.sum_option, Fintype.sum_option]
  simp_rw [hW', sum_add_distrib]
  ring

/-- The utility of a point of the sequence-form polytope is at most `ℓ none` plus the sum, over
the first decision points, of their best values. -/
theorem sum_mul_le_of_isBestResponseValue {ℓ : Option (Σ j, A j) → ℝ} {W : (Σ j, A j) → ℝ}
    (hW : IsBestResponseValue parent ℓ W) {x : Option (Σ j, A j) → ℝ}
    (hx : x ∈ sequenceFormPolytope parent) :
    ∑ s, ℓ s * x s ≤ ℓ none + ∑ j with parent j = none, ⨆ a, W ⟨j, a⟩ := by
  obtain ⟨hx1, hx0, hxsum⟩ := hx
  have hle : ∑ s : Σ j, A j, W s * x (some s) ≤ ∑ j, (⨆ a, W ⟨j, a⟩) * x (parent j) := by
    rw [Fintype.sum_sigma]
    refine sum_le_sum fun j _ ↦ ?_
    rw [← hxsum, mul_sum]
    exact sum_le_sum fun a _ ↦
      mul_le_mul_of_nonneg_right (Finite.le_ciSup (fun a ↦ W ⟨j, a⟩) a) (hx0 _)
  have := sum_mul_add_sum_eq hW x
  rw [hx1, mul_one] at this
  linarith

/-- The sequence form of a pure strategy playing at each decision point an action of best value
attains the best-response value. -/
theorem IsSequenceForm.sum_mul_eq_of_isBestResponseValue {ℓ : Option (Σ j, A j) → ℝ}
    {W : (Σ j, A j) → ℝ} (hW : IsBestResponseValue parent ℓ W) {a : ∀ j, A j}
    (ha : ∀ j, W ⟨j, a j⟩ = ⨆ a', W ⟨j, a'⟩) {x : Option (Σ j, A j) → ℝ}
    (hx : IsSequenceForm parent (fun j ↦ Pi.single (a j) 1) x) :
    ∑ s, ℓ s * x s = ℓ none + ∑ j with parent j = none, ⨆ a, W ⟨j, a⟩ := by
  have heq : ∑ s : Σ j, A j, W s * x (some s) = ∑ j, (⨆ a, W ⟨j, a⟩) * x (parent j) := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun j _ ↦ ?_
    simp_rw [hx.apply_some, ← ha j]
    simp [Pi.single_apply, mul_comm]
  have := sum_mul_add_sum_eq hW x
  rw [hx.apply_none, mul_one] at this
  linarith

/-- **Best response in sequence form**: the maximum of the linear function `x ↦ ∑ s, ℓ s * x s`
over the sequence-form polytope is `ℓ none` plus the sum, over the first decision points, of
their best values. -/
theorem isGreatest_linear_bestResponse [∀ j, Nonempty (A j)]
    (hρ : ∀ j j' a, parent j = some ⟨j', a⟩ → ρ j' < ρ j) {ℓ : Option (Σ j, A j) → ℝ}
    {W : (Σ j, A j) → ℝ} (hW : IsBestResponseValue parent ℓ W) :
    IsGreatest ((fun x ↦ ∑ s, ℓ s * x s) '' sequenceFormPolytope parent)
      (ℓ none + ∑ j with parent j = none, ⨆ a, W ⟨j, a⟩) := by
  choose a ha using fun j ↦ exists_eq_ciSup_of_finite (f := fun a ↦ W ⟨j, a⟩)
  obtain ⟨x, hx⟩ := exists_isSequenceForm hρ fun j ↦ Pi.single (a j) (1 : ℝ)
  refine ⟨⟨x, hx.mem_sequenceFormPolytope hρ fun j ↦ ⟨StdSimplex.single (a j), ?_⟩,
    hx.sum_mul_eq_of_isBestResponseValue hW ha⟩, ?_⟩
  · simp [Finsupp.single_eq_pi_single]
  · rintro _ ⟨y, hy, rfl⟩
    exact sum_mul_le_of_isBestResponseValue hW hy

end BestResponse

end TauCeti
