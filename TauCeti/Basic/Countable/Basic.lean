/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Uncountable dependent products

A dependent product `∀ a, π a` of nontrivial types over an infinite index type `α` is uncountable
(`Pi.instUncountable`).

## Main results

* `Pi.instUncountable`: a dependent product of nontrivial types over an infinite index type is
  uncountable.
-/

public section

/-- A dependent product of nontrivial types over an infinite index type is uncountable. -/
instance Pi.instUncountable {α : Type*} {π : α → Type*} [Infinite α] [∀ a, Nontrivial (π a)] :
    Uncountable (∀ a, π a) := by
  classical
  rw [uncountable_iff_forall_not_surjective]
  intro f hf
  let e : ℕ ↪ α := Infinite.natEmbedding α
  let d : ∀ a, π a := fun a =>
    if h : ∃ n, e n = a then (exists_ne (f h.choose a)).choose else Classical.arbitrary (π a)
  obtain ⟨n, hn⟩ := hf d
  have hmem : ∃ m, e m = e n := ⟨n, rfl⟩
  have hch : hmem.choose = n := e.injective hmem.choose_spec
  have hne : d (e n) ≠ f n (e n) := by
    simp only [d, dite_eq_left hmem, hch]
    exact (exists_ne (f n (e n))).choose_spec
  exact hne (congrFun hn (e n)).symm
