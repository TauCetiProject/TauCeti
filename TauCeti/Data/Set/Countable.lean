/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Countable ranges and predicates with countable truth sides

Let `P i` be countably many predicates on a type `X`, each of which *splits* `X` with a countable
side: either `{x | P i x}` or `{x | ¬ P i x}` is countable. Off the union of the countable sides,
every `P i` is constant. Consequently all the predicates are decided simultaneously off one
countable set, and anything determined by their truth values takes countably many values.

This is set-theoretic counting with no topology. In descriptive set theory it bounds the number
of classes of an equivalence relation that is decided by countably many tests, such as the truth
values of countably many sentences.

## Main results

* `Set.Countable.range_min`: the pointwise minimum of two countable-range functions has
  countable range.
* `Finset.countable_range_sup`: the pointwise finite supremum of countable-range functions
  has countable range.
* `Function.Injective.exists_injOn_comp_eq_inl`: an injective map `g : α → β` has a left inverse
  `β → α ⊕ ℕ`, through `Sum.inl`, that is injective on the range of `g` together with a given
  countable set.
* `TauCeti.exists_countable_forall_exists_mem`: for a relation between a countable type and an
  arbitrary type, countably many elements of the second type serve as witnesses for every element
  of the first that has a witness.
* `TauCeti.exists_countable_exceptions_of_splits`: outside one countable set, every `P i` is
  constant.
* `TauCeti.countable_range_of_splits`: a map that depends only on the truth values of the `P i`
  has countable range.
* `TauCeti.constant_off_countable_of_splits`: on a nonempty type, such a map is constant off a
  countable set; `TauCeti.constant_off_countable_of_separating_splits` is the case of a map whose
  values are separated by countably many tests.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/CountableSplits.lean`.
* Divergences from that source: the constancy result is stated for any map determined by the
  predicates, with the separating-tests form as a corollary, and assumes only that the domain is
  nonempty rather than uncountable.
  `TauCeti.exists_countable_forall_exists_mem` is not from that source; it is the choice of
  witnesses in the proof of Lemma 2.9 of V. Guirardel and G. Levitt, *JSJ decompositions of
  groups*, Astérisque 395 (2017).
-/

public section

universe u v w

/-- The pointwise minimum of two functions with countable ranges has countable range. -/
theorem Set.Countable.range_min {α β : Type*} [Min β] {f g : α → β}
    (hf : (Set.range f).Countable) (hg : (Set.range g).Countable) :
    (Set.range fun x ↦ min (f x) (g x)).Countable :=
  (hf.image2 hg min).mono (by rintro _ ⟨x, rfl⟩; exact ⟨f x, ⟨x, rfl⟩, g x, ⟨x, rfl⟩, rfl⟩)

/-- The pointwise finite supremum of countable-range functions has countable range.
The empty supremum is the constant bottom function. -/
theorem Finset.countable_range_sup {κ α Ω : Type*} [SemilatticeSup α] [OrderBot α]
    (s : Finset κ) {f : κ → Ω → α} (hf : ∀ j ∈ s, (Set.range (f j)).Countable) :
    (Set.range (fun ω ↦ s.sup (fun j ↦ f j ω))).Countable := by
  have h := Finset.sup_induction (p := fun g : Ω → α ↦ (Set.range g).Countable)
    ((Set.countable_singleton (⊥ : α)).mono (by simp))
    (fun a ha b hb ↦ (ha.image2 hb (· ⊔ ·)).mono (by
      rintro _ ⟨ω, rfl⟩
      exact ⟨a ω, ⟨ω, rfl⟩, b ω, ⟨ω, rfl⟩, rfl⟩)) hf
  have heq : s.sup f = fun ω ↦ s.sup (fun j ↦ f j ω) := funext (s.sup_apply f)
  exact heq ▸ h

/-- An injective map `g : α → β` has a left inverse `β → α ⊕ ℕ`, through `Sum.inl`, that is
injective on the range of `g` together with a given countable set. -/
theorem Function.Injective.exists_injOn_comp_eq_inl {α β : Type*} {g : α → β}
    (hg : Function.Injective g) {S : Set β} (hS : S.Countable) :
    ∃ p : β → α ⊕ ℕ, (Set.range g ∪ S).InjOn p ∧ p ∘ g = Sum.inl := by
  classical
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injOn.mp hS
  refine ⟨Function.extend g Sum.inl (Sum.inr ∘ e), fun y hy z hz hyz => ?_,
    funext fun x => hg.extend_apply _ _ x⟩
  by_cases hy' : ∃ x, g x = y <;> by_cases hz' : ∃ x, g x = z
  · obtain ⟨x, rfl⟩ := hy'
    obtain ⟨x', rfl⟩ := hz'
    rw [hg.extend_apply, hg.extend_apply, Sum.inl.injEq] at hyz
    rw [hyz]
  · obtain ⟨x, rfl⟩ := hy'
    simp [hg.extend_apply, Function.extend_apply' _ _ _ hz'] at hyz
  · obtain ⟨x, rfl⟩ := hz'
    simp [hg.extend_apply, Function.extend_apply' _ _ _ hy'] at hyz
  · simp only [Function.extend_apply' _ _ _ hy', Function.extend_apply' _ _ _ hz',
      Function.comp_apply, Sum.inr.injEq] at hyz
    exact he (hy.resolve_left hy') (hz.resolve_left hz') hyz

namespace TauCeti

open Set

/-- **Countably many witnesses.** For a relation `P` between a countable type and an arbitrary
type, some countable set of elements of the second type contains, for every `a` with `P a i` for
some `i`, an element `j` with `P a j`. -/
theorem exists_countable_forall_exists_mem {α : Sort*} {ι : Type*} [Countable α]
    (P : α → ι → Prop) : ∃ J : Set ι, J.Countable ∧ ∀ a i, P a i → ∃ j ∈ J, P a j :=
  ⟨range fun a : {a // ∃ i, P a i} => a.property.choose, countable_range _,
    fun a i hi => ⟨_, ⟨⟨a, i, hi⟩, rfl⟩, (⟨i, hi⟩ : ∃ i, P a i).choose_spec⟩⟩

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

/-- **Constant off a countable set.** On a nonempty type, a map that depends only on the truth
values of countably many predicates, each with a countable truth side, agrees with one of its
values outside a countable set. -/
theorem constant_off_countable_of_splits [Nonempty X] {Y : Type w} {P : ι → X → Prop}
    (g : X → Y) (hg : ∀ x y, (∀ i, P i x ↔ P i y) → g x = g y)
    (hsplit : ∀ i, {x | P i x}.Countable ∨ {x | ¬ P i x}.Countable) :
    ∃ x₀, {x | g x ≠ g x₀}.Countable := by
  obtain ⟨N, hN, hconst⟩ := exists_countable_exceptions_of_splits hsplit
  by_cases h : ∃ x₀, x₀ ∉ N
  · obtain ⟨x₀, hx₀⟩ := h
    refine ⟨x₀, hN.mono fun x hx => ?_⟩
    by_contra hxN
    exact hx (hg _ _ (hconst x hxN x₀ hx₀))
  · -- every point is exceptional, so the whole type is countable
    push Not at h
    exact ⟨Classical.arbitrary X, hN.mono fun x _ => h x⟩

/-- **Constant off a countable set, separating tests.** On a nonempty type, a map whose values are
separated by countably many tests, each with a countable truth side along the map, agrees with
one of its values outside a countable set. -/
theorem constant_off_countable_of_separating_splits [Nonempty X] {Y : Type w} (f : X → Y)
    (test : ι → Y → Prop) (hsep : ∀ y z, (∀ i, test i y ↔ test i z) → y = z)
    (hsplit : ∀ i, {x | test i (f x)}.Countable ∨ {x | ¬ test i (f x)}.Countable) :
    ∃ x₀, {x | f x ≠ f x₀}.Countable :=
  constant_off_countable_of_splits f (fun _ _ h => hsep _ _ h) hsplit

end TauCeti
