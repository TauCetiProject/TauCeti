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
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.SuccPred.Nat

/-!
# Point updates and even-odd interleaving of monotone maps

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

Interleaving two sequences `a` and `c` as `a 0, c 0, a 1, c 1, …, a n` produces a monotone
sequence on `Iic (2 * n)` whenever `a i ≤ c i ≤ a (i + 1)` for every `i < n`
(`TauCeti.monotoneOn_even_odd_Iic`).

## Main results

* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `TauCeti.monotoneOn_even_odd_Iic`: interleaving `a` at even indices and `c` at odd indices is
  monotone on `Iic (2 * n)` when `a i ≤ c i` and `c i ≤ a (i + 1)` for `i < n`.
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

/-- Interleaving `a 0, c 0, a 1, c 1, …, a n` produces a monotone sequence on `{0, …, 2 * n}`
whenever `a i ≤ c i` and `c i ≤ a (i + 1)` for every `i < n`. -/
theorem TauCeti.monotoneOn_even_odd_Iic {α : Type*} [Preorder α] {n : ℕ} {a c : ℕ → α}
    (hac : ∀ i < n, a i ≤ c i ∧ c i ≤ a (i + 1)) :
    MonotoneOn (fun j ↦ if j % 2 = 0 then a (j / 2) else c (j / 2)) (Iic (2 * n)) := by
  refine monotoneOn_of_le_add_one ordConnected_Iic fun j _ _ hj ↦ ?_
  have hi : j / 2 < n := by
    have : j < 2 * n := Nat.lt_of_succ_le hj
    omega
  obtain ⟨h₁, h₂⟩ := hac (j / 2) hi
  rcases Nat.mod_two_eq_zero_or_one j with hmod | hmod
  · have hdiv1 : (j + 1) / 2 = j / 2 := by omega
    have hmod1 : (j + 1) % 2 = 1 := by omega
    simpa only [hmod, hmod1, Nat.one_ne_zero, ↓reduceIte, hdiv1] using h₁
  · have hdiv1 : (j + 1) / 2 = j / 2 + 1 := by omega
    have hmod1 : (j + 1) % 2 = 0 := by omega
    simpa only [hmod, Nat.one_ne_zero, hmod1, ↓reduceIte, hdiv1] using h₂
