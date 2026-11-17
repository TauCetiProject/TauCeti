/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Nat
public import Mathlib.Order.SetNotation
public import TauCeti.Data.Stream.Init
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.SuccPred.Nat

/-!
# Point updates and even-odd interleaving of monotone maps

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

Interleaving two sequences `a` and `c` as `TauCeti.interleave a c`, namely
`a 0, c 0, a 1, c 1, …, a n`, produces a monotone sequence on `Iic (2 * n)` whenever
`a i ≤ c i ≤ a (i + 1)` for every `i < n` (`TauCeti.monotoneOn_interleave_Iic`).

## Main results

* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `TauCeti.monotoneOn_interleave_Iic`: `TauCeti.interleave a c` is monotone on `Iic (2 * n)` when
  `a i ≤ c i` and `c i ≤ a (i + 1)` for `i < n`.
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

/-- Interleaving `a 0, c 0, a 1, c 1, …, a n` via `TauCeti.interleave a c` produces a monotone
sequence on `{0, …, 2 * n}` whenever `a i ≤ c i` and `c i ≤ a (i + 1)` for every `i < n`. -/
theorem TauCeti.monotoneOn_interleave_Iic {α : Type*} [Preorder α] {n : ℕ} {a c : ℕ → α}
    (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    MonotoneOn (TauCeti.interleave a c) (Iic (2 * n)) := by
  refine monotoneOn_of_le_add_one ordConnected_Iic fun j _ _ hj ↦ ?_
  have hjlt : j < 2 * n := Nat.lt_of_succ_le hj
  set i := j / 2
  by_cases hmod : j % 2 = 0
  · rw [show j = 2 * i by omega]
    simpa using (hac i (by omega)).1
  · have h1 : j = 2 * i + 1 := by omega
    have h2 : j + 1 = 2 * (i + 1) := by omega
    rw [h2, h1]
    simpa using (hac i (by omega)).2
