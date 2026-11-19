/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation

/-!
# Changing a strictly monotone function at one point

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

The consecutive intervals `[f i, f (i + 1)]`, `i < n`, of a grid `f` monotone through its last
point `f n` follow one another: of two distinct ones, one ends before the other starts
(`MonotoneOn.pairwise_succ_le_or_succ_le`).

## Main results

* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `MonotoneOn.pairwise_succ_le_or_succ_le`: distinct consecutive intervals of a monotone grid
  overlap at most at an endpoint.
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

/-- Distinct consecutive intervals `[f i, f (i + 1)]`, `i < n`, of a grid monotone through its last
point `f n` overlap at most at an endpoint: one of them ends before the other starts. -/
theorem MonotoneOn.pairwise_succ_le_or_succ_le {α : Type*} [Preorder α] {f : ℕ → α} {n : ℕ}
    (hf : MonotoneOn f (Iic n)) :
    (Iio n).Pairwise fun i j ↦ f (i + 1) ≤ f j ∨ f (j + 1) ≤ f i := by
  intro i hi j hj hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Or.inl (hf (mem_Iic.mpr (Nat.succ_le_of_lt hi)) (mem_Iic.mpr (le_of_lt hj))
      (Nat.succ_le_of_lt h))
  · exact Or.inr (hf (mem_Iic.mpr (Nat.succ_le_of_lt hj)) (mem_Iic.mpr (le_of_lt hi))
      (Nat.succ_le_of_lt h))
