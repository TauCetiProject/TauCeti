/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Countable

/-!
# Countably many predicates with countable truth sides

Let `P i` be countably many predicates on a type `X`, each of which *splits* `X` with a countable
side: either `{x | P i x}` or `{x | ¬ P i x}` is countable. Off the union of the countable sides,
every `P i` is constant. Consequently all the predicates are decided simultaneously off one
countable set, and anything determined by their truth values takes countably many values.

This is set-theoretic counting with no topology. In descriptive set theory it bounds the number
of classes of an equivalence relation that is decided by countably many tests, such as the truth
values of countably many sentences.

## Main results

* `Set.exists_countable_exceptions_of_splits`: outside one countable set, every `P i` is
  constant.
* `Set.countable_range_of_splits`: a map that depends only on the truth values of the `P i` has
  countable range.
* `Set.constant_off_countable_of_splits`: on an uncountable type, a map whose values are separated
  by countably many tests, each with a countable side along the map, is constant off a countable
  set.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/CountableSplits.lean`.
* Divergences from that source: the results are in the `Set` namespace; uncountability of the
  domain is the instance `[Uncountable X]` rather than the hypothesis `¬ Countable X`.
-/

public section

universe u v w

namespace Set

variable {X : Type u} {ι : Type v} [Countable ι]

/-- **Simultaneous constancy off a countable set.** If each of countably many predicates has a
countable truth side, then outside one countable set every predicate takes a single value. -/
theorem exists_countable_exceptions_of_splits {P : ι → X → Prop}
    (hsplit : ∀ i, {x | P i x}.Countable ∨ {x | ¬ P i x}.Countable) :
    ∃ N : Set X, N.Countable ∧ ∀ x ∉ N, ∀ y ∉ N, ∀ i, P i x ↔ P i y := by
  classical
  -- the countable side of each predicate
  let S : ι → Set X := fun i => if {x | P i x}.Countable then {x | P i x} else {x | ¬ P i x}
  have hS (i : ι) : (S i).Countable := by
    by_cases h : {x | P i x}.Countable
    · simp [S, h]
    · simpa [S, h] using (hsplit i).resolve_left h
  -- off its countable side, a predicate takes the other value
  have hoff (i : ι) (x : X) (hx : x ∉ S i) (y : X) (hy : y ∉ S i) : P i x ↔ P i y := by
    by_cases h : {x | P i x}.Countable
    · simp only [S, h, ite_true, mem_ofPred_eq] at hx hy
      exact iff_of_false hx hy
    · simp only [S, h, ite_false, mem_ofPred_eq, not_not] at hx hy
      exact iff_of_true hx hy
  refine ⟨⋃ i, S i, countable_iUnion hS, fun x hx y hy i => hoff i x ?_ y ?_⟩
  · exact fun h => hx (mem_iUnion_of_mem i h)
  · exact fun h => hy (mem_iUnion_of_mem i h)

/-- **Countable range.** A map that depends only on the truth values of countably many predicates,
each with a countable truth side, has countable range: the countable exceptional set contributes
countably many values, and its complement at most one. -/
theorem countable_range_of_splits {Y : Type w} {P : ι → X → Prop} (g : X → Y)
    (hg : ∀ x y, (∀ i, P i x ↔ P i y) → g x = g y)
    (hsplit : ∀ i, {x | P i x}.Countable ∨ {x | ¬ P i x}.Countable) :
    (range g).Countable := by
  obtain ⟨N, hN, hconst⟩ := exists_countable_exceptions_of_splits hsplit
  by_cases h : ∃ x₀, x₀ ∉ N
  · obtain ⟨x₀, hx₀⟩ := h
    refine ((hN.image g).union (countable_singleton (g x₀))).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ N
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr (hg x x₀ (hconst x hx x₀ hx₀))
  · push Not at h
    refine (hN.image g).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨x, h x, rfl⟩

/-- **Constant off a countable set.** On an uncountable type, a map whose values are separated by
countably many tests, each with a countable truth side along the map, agrees with one of its
values outside a countable set. -/
theorem constant_off_countable_of_splits [Uncountable X] {Y : Type w} (f : X → Y)
    (test : ι → Y → Prop) (hsep : ∀ y z, (∀ i, test i y ↔ test i z) → y = z)
    (hsplit : ∀ i, {x | test i (f x)}.Countable ∨ {x | ¬ test i (f x)}.Countable) :
    ∃ x₀, {x | f x ≠ f x₀}.Countable := by
  obtain ⟨N, hN, hconst⟩ := exists_countable_exceptions_of_splits hsplit
  -- the exceptional set is countable, so some point lies outside it
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ N := by
    by_contra h
    push Not at h
    exact not_countable_univ (hN.mono fun x _ => h x)
  refine ⟨x₀, hN.mono fun x hx => ?_⟩
  by_contra hxN
  exact hx (hsep _ _ (hconst x hxN x₀ hx₀))

end Set
