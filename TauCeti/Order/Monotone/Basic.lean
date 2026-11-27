/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Monotonicity on sets: point updates, grids and two-sided minima

No function is both strictly monotone and strictly antitone on a set with two points
(`Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`).

Redefining a function at a single point `a` keeps it strictly monotone on a set `s` as long as
the new value lies strictly between the values at the points of `s` on either side of `a`
(`StrictMonoOn.update`). For instance, a crossing time may be moved along a parameter interval
containing no other crossing time without changing the order of the crossings.

A function strictly monotone on `s` maps the part of `s` above `a ∈ s` onto the part of `f '' s`
above `f a` (`StrictMonoOn.image_Ioi_inter`).

The consecutive intervals `[f i, f (i + 1)]`, `i < n`, of a grid `f` monotone through its last
point `f n` follow one another: of two distinct ones, one ends before the other starts
(`MonotoneOn.pairwise_succ_le_or_succ_le`). For a monotone `ℤ`-indexed sequence, a point strictly
inside one of these intervals lies in no other (`Monotone.mem_Icc_iff_eq_of_mem_Ioo`).

A decreasing surjection of a closed interval `[a, b]` onto itself exchanges its endpoints
(`Antitone.coe_apply_eq_left_of_surjective`, `Antitone.coe_apply_eq_right_of_surjective`).

A function on a linearly ordered domain that decreases on `s ∩ (-∞, a]` and increases
on `s ∩ [a, ∞)` attains its global minimum on `s` at `a` (`TauCeti.le_of_antitoneOn_monotoneOn`),
strictly so away from `a` when both halves are strict (`TauCeti.lt_of_strictAntiOn_strictMonoOn`).

## Main results

* `Set.Nontrivial.not_strictMonoOn_and_strictAntiOn`: no function is both strictly monotone and
  strictly antitone on a set with two points.
* `StrictMonoOn.update`: a function strictly monotone on `s \ {a}`, updated at `a` to a value
  above its values before `a` and below its values after `a`, is strictly monotone on `s`.
* `StrictMonoOn.image_Ioi_inter`: `f '' ((a, ∞) ∩ s) = (f a, ∞) ∩ f '' s` for `f` strictly
  monotone on `s` and `a ∈ s`.
* `MonotoneOn.pairwise_succ_le_or_succ_le`: distinct consecutive intervals of a monotone grid
  overlap at most at an endpoint.
* `Monotone.mem_Icc_iff_eq_of_mem_Ioo`: a point strictly inside the interval `(a k, a (k + 1))`
  of a monotone `ℤ`-indexed sequence lies in `[a q, a (q + 1)]` exactly when `q = k`.
* `Antitone.coe_apply_eq_left_of_surjective`, `Antitone.coe_apply_eq_right_of_surjective`: an
  antitone surjection of `[a, b]` onto itself sends `b` to `a` and `a` to `b`.
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

/-- A function strictly monotone on `s` maps `(a, ∞) ∩ s` onto `(f a, ∞) ∩ f '' s`, for
`a ∈ s`. -/
theorem StrictMonoOn.image_Ioi_inter {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    {s : Set α} (hf : StrictMonoOn f s) {a : α} (ha : a ∈ s) :
    f '' (Ioi a ∩ s) = Ioi (f a) ∩ f '' s := by
  ext y
  constructor
  · rintro ⟨x, ⟨hax, hx⟩, rfl⟩
    exact ⟨hf ha hx hax, mem_image_of_mem f hx⟩
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨(hf.lt_iff_lt ha hx).1 hy, hx⟩, rfl⟩

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

/-- A point strictly inside the interval `(a k, a (k + 1))` of a monotone `ℤ`-indexed sequence `a`
lies in the closed interval `[a q, a (q + 1)]` exactly when `q = k`. -/
theorem Monotone.mem_Icc_iff_eq_of_mem_Ioo {α : Type*} [Preorder α] {a : ℤ → α}
    (ha : Monotone a) {x : α} {k : ℤ} (hx : x ∈ Ioo (a k) (a (k + 1))) {q : ℤ} :
    x ∈ Icc (a q) (a (q + 1)) ↔ q = k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ⟨hx.1.le, hx.2.le⟩⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (h.2.trans_lt ((ha (by omega)).trans_lt hx.1)).false
  · exact ((hx.2.trans_le (ha (by omega))).trans_le h.1).false

/-- An antitone surjection of `[a, b]` onto itself sends `b` to `a`. -/
theorem Antitone.coe_apply_eq_left_of_surjective {α : Type*} [PartialOrder α] {a b : α}
    {f : Icc a b → Icc a b} (hf : Antitone f) (hs : Surjective f) {y : Icc a b}
    (hy : (y : α) = b) : (f y : α) = a := by
  obtain ⟨z, hz⟩ := hs ⟨a, left_mem_Icc.2 (y.property.1.trans y.property.2)⟩
  have hzy : z ≤ y := Subtype.coe_le_coe.1 (by rw [hy]; exact z.property.2)
  exact le_antisymm (by simpa [hz] using Subtype.coe_le_coe.2 (hf hzy)) (f y).property.1

/-- An antitone surjection of `[a, b]` onto itself sends `a` to `b`. -/
theorem Antitone.coe_apply_eq_right_of_surjective {α : Type*} [PartialOrder α] {a b : α}
    {f : Icc a b → Icc a b} (hf : Antitone f) (hs : Surjective f) {y : Icc a b}
    (hy : (y : α) = a) : (f y : α) = b := by
  obtain ⟨z, hz⟩ := hs ⟨b, right_mem_Icc.2 (y.property.1.trans y.property.2)⟩
  have hzy : y ≤ z := Subtype.coe_le_coe.1 (by rw [hy]; exact z.property.1)
  exact le_antisymm (f y).property.2 (by simpa [hz] using Subtype.coe_le_coe.2 (hf hzy))

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
