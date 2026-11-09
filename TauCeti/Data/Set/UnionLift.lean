/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Order.Monotone.Defs

/-!
# Gluing functions along an increasing sequence of sets

Mathlib's `Set.liftCover` and `Set.iUnionLift` glue functions on the members of a family of sets
which agree on every pairwise overlap. For an increasing sequence `S 0 ⊆ S 1 ⊆ ⋯` it suffices that
consecutive functions agree, along each inclusion `S n ⊆ S (n + 1)`
(`Monotone.eq_of_forall_succ_eq`). This is the shape in which functions on the stages of a tower
are usually built, one stage at a time.
-/

public section

namespace Monotone

variable {α β : Type*} {S : ℕ → Set α}

/-- Functions on the members of an increasing sequence of sets which agree along each inclusion
`S n ⊆ S (n + 1)` agree on every overlap `S m ∩ S n`, as `Set.liftCover` requires. -/
theorem eq_of_forall_succ_eq (hS : Monotone S) (f : ∀ n, S n → β)
    (hf : ∀ n (x : α) (hx : x ∈ S n), f (n + 1) ⟨x, hS n.le_succ hx⟩ = f n ⟨x, hx⟩)
    (m n : ℕ) (x : α) (hm : x ∈ S m) (hn : x ∈ S n) : f m ⟨x, hm⟩ = f n ⟨x, hn⟩ := by
  have key {m n : ℕ} (hmn : m ≤ n) (hx : x ∈ S m) : f n ⟨x, hS hmn hx⟩ = f m ⟨x, hx⟩ := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih => rw [hf n x (hS hmn hx), ih]
  rcases le_total m n with h | h
  · exact (key h hm).symm
  · exact key h hn

end Monotone
