/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Extending finite injections to permutations

A map that is injective on a finite set `s ⊆ α` agrees on `s` with a permutation of `α`. For
finite `α` this is `Cardinal.extend_function_finite`; for infinite `α` the finite set `s` has
smaller cardinality than `α`, and `Cardinal.extend_function_of_lt` applies. Unlike those
statements, the form below needs no cardinality hypothesis.

Similarly, an injective map `g : α → β` has, on any finite set `S ⊆ β`, a left inverse into
`α ⊕ ℕ` that is injective on `S`: it sends `g x` to `Sum.inl x` and the rest of `S` injectively
into `ℕ`.

These are used to relabel the finitely many vertices of a simplicial complex inside a larger
vertex type by a global bijection, and to pull a construction on finitely many vertices back to
the original vertex type.
-/

public section

namespace Set.InjOn

/-- A self-map of `α` that is injective on a finite set `s` agrees on `s` with a permutation
of `α`. -/
theorem exists_equiv_eqOn {α : Type*} {s : Set α} {f : α → α} (hf : s.InjOn f)
    (hs : s.Finite) : ∃ e : α ≃ α, s.EqOn e f := by
  let g : s ↪ α := ⟨s.domRestrict f, Set.injOn_iff_injective.mp hf⟩
  have key : ∃ e : α ≃ α, ∀ x : s, e x = g x := by
    cases fintypeOrInfinite α
    · exact Cardinal.extend_function_finite g ⟨Equiv.refl α⟩
    · refine Cardinal.extend_function_of_lt g ?_ ⟨Equiv.refl α⟩
      exact (Cardinal.lt_aleph0_iff_set_finite.mpr hs).trans_le (Cardinal.aleph0_le_mk α)
  obtain ⟨e, he⟩ := key
  exact ⟨e, fun x hx => he ⟨x, hx⟩⟩

end Set.InjOn

/-- An injective map `g : α → β` has a left inverse `β → α ⊕ ℕ`, through `Sum.inl`, that is
injective on a given finite set. -/
theorem Function.Injective.exists_injOn_comp_eq_inl {α β : Type*} {g : α → β}
    (hg : Function.Injective g) {S : Set β} (hS : S.Finite) :
    ∃ p : β → α ⊕ ℕ, S.InjOn p ∧ p ∘ g = Sum.inl := by
  classical
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injOn.mp hS.countable
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
    exact he hy hz hyz
