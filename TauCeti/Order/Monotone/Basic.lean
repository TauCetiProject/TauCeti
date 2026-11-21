/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs

/-!
# Monotonicity on sets: point updates and two-sided minima

No function is both strictly monotone and strictly antitone on a set with two points
(`Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`).

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

Conversely, a function on a linearly ordered domain that decreases on `s ∩ (-∞, a]` and increases
on `s ∩ [a, ∞)` attains its global minimum on `s` at `a` (`TauCeti.le_of_antitoneOn_monotoneOn`),
strictly so away from `a` when both halves are strict (`TauCeti.lt_of_strictAntiOn_strictMonoOn`).

## Main results

* `Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`: no function is both strictly monotone and
  strictly antitone on a set with two points.
* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `TauCeti.le_of_antitoneOn_monotoneOn`: if `f` is antitone on `s ∩ Iic a` and monotone on
  `s ∩ Ici a` with `a ∈ s`, then `f a ≤ f x` for all `x ∈ s`.
* `TauCeti.lt_of_strictAntiOn_strictMonoOn`: if `f` is strictly antitone on `s ∩ Iic a` and
  strictly monotone on `s ∩ Ici a` with `a ∈ s`, then `f a < f x` for all `x ∈ s` with `x ≠ a`.
-/

public section

open Function Set

/-- A function is not both strictly monotone and strictly antitone on a set with two points. -/
theorem Set.Nontrivial.not_strictMonoOn_and_strictAntiOn {α β : Type*} [LinearOrder α]
    [Preorder β] {f : α → β} {s : Set α} (hs : s.Nontrivial) :
    ¬(StrictMonoOn f s ∧ StrictAntiOn f s) := by
  rintro ⟨hm, ha⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  rcases hxy.lt_or_gt with h | h
  · exact lt_asymm (hm hx hy h) (ha hx hy h)
  · exact lt_asymm (hm hy hx h) (ha hy hx h)

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

namespace TauCeti

/-- If `f` is antitone on `s ∩ (-∞, a]` and monotone on `s ∩ [a, ∞)` with `a ∈ s`, then `f`
attains its minimum on `s` at `a`. -/
theorem le_of_antitoneOn_monotoneOn {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    {s : Set α} {a x : α} (ha : a ∈ s) (hanti : AntitoneOn f (s ∩ Iic a))
    (hmono : MonotoneOn f (s ∩ Ici a)) (hx : x ∈ s) :
    f a ≤ f x :=
  (le_total x a).elim (fun h ↦ hanti ⟨hx, h⟩ ⟨ha, le_rfl⟩ h)
    (fun h ↦ hmono ⟨ha, le_rfl⟩ ⟨hx, h⟩ h)

/-- If `f` is strictly antitone on `s ∩ (-∞, a]` and strictly monotone on `s ∩ [a, ∞)` with
`a ∈ s`, then `f a < f x` for every `x ∈ s` distinct from `a`. -/
theorem lt_of_strictAntiOn_strictMonoOn {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    {s : Set α} {a x : α} (ha : a ∈ s) (hanti : StrictAntiOn f (s ∩ Iic a))
    (hmono : StrictMonoOn f (s ∩ Ici a)) (hx : x ∈ s) (hne : x ≠ a) :
    f a < f x :=
  hne.lt_or_gt.elim (fun h ↦ hanti ⟨hx, h.le⟩ ⟨ha, le_rfl⟩ h)
    (fun h ↦ hmono ⟨ha, le_rfl⟩ ⟨hx, h.le⟩ h)

end TauCeti
