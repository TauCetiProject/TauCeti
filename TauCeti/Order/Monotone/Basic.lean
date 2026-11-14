/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation

/-!
# Pointwise updates and level-set decompositions of monotone functions

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

For any monotone map `g : γ → δ` between preorders and any `f : α → γ`, every superlevel set
`{x ∈ u | y ≤ g (f x)}` decomposes as the union over attained values `v ∈ f '' u` with `y ≤ g v`
of the superlevel sets `{x ∈ u | v ≤ f x}` (`Monotone.setOf_mem_and_le_eq_biUnion`), and dually
for sublevel sets (`Monotone.setOf_mem_and_ge_eq_biUnion`).

## Main results

* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `Monotone.setOf_mem_and_le_eq_biUnion`, `Monotone.setOf_mem_and_ge_eq_biUnion`: decomposition
  of superlevel and sublevel sets of `g ∘ f` on `u` into unions of superlevel and sublevel sets of
  `f` at attained values in `f '' u`.
-/

public section

open Function Set

/-- Updating a function at `a` keeps it strictly monotone on `s`, provided it is strictly
monotone on `s` away from `a` and the new value `b` lies above the values at points of `s` before
`a` and below those at points of `s` after `a`. -/
theorem StrictMonoOn.update {α β : Type*} [Preorder α] [Preorder β] [DecidableEq α] {f : α → β}
    {s : Set α} {a : α} (hf : StrictMonoOn f (s \ {a})) {b : β}
    (hlt : ∀ t ∈ s, t < a → f t < b) (hgt : ∀ t ∈ s, a < t → b < f t) :
    StrictMonoOn (update f a b) s := by
  intro x hx y hy hxy
  by_cases hxa : x = a
  · subst hxa
    rw [update_self, update_of_ne hxy.ne']
    exact hgt y hy hxy
  by_cases hya : y = a
  · subst hya
    rw [update_self, update_of_ne hxa]
    exact hlt x hx hxy
  rw [update_of_ne hxa, update_of_ne hya]
  exact hf ⟨hx, hxa⟩ ⟨hy, hya⟩ hxy

/-- On any set `u`, the superlevel set `{x ∈ u | y ≤ g (f x)}` of a monotone post-composition is
the union over attained values `v ∈ f '' u` with `y ≤ g v` of `{x ∈ u | v ≤ f x}`. -/
theorem Monotone.setOf_mem_and_le_eq_biUnion {α γ δ : Type*} [Preorder γ] [Preorder δ]
    {g : γ → δ} (hg : Monotone g) (f : α → γ) (u : Set α) (y : δ) :
    {x ∈ u | y ≤ g (f x)} = ⋃ v ∈ {v ∈ f '' u | y ≤ g v}, {x ∈ u | v ≤ f x} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  exact ⟨fun ⟨hx, hy⟩ ↦ ⟨f x, ⟨⟨x, hx, rfl⟩, hy⟩, hx, le_rfl⟩,
    fun ⟨v, ⟨_, hy⟩, hx, hvx⟩ ↦ ⟨hx, hy.trans (hg hvx)⟩⟩

/-- On any set `u`, the sublevel set `{x ∈ u | g (f x) ≤ y}` of a monotone post-composition is
the union over attained values `v ∈ f '' u` with `g v ≤ y` of `{x ∈ u | f x ≤ v}`. -/
theorem Monotone.setOf_mem_and_ge_eq_biUnion {α γ δ : Type*} [Preorder γ] [Preorder δ]
    {g : γ → δ} (hg : Monotone g) (f : α → γ) (u : Set α) (y : δ) :
    {x ∈ u | g (f x) ≤ y} = ⋃ v ∈ {v ∈ f '' u | g v ≤ y}, {x ∈ u | f x ≤ v} :=
  hg.dual.setOf_mem_and_le_eq_biUnion f u y
