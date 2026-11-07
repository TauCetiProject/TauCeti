/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.MinMax
import Mathlib.Tactic.Order

/-!
# Sorted pairs and relative orders of triples

An unordered pair of distinct points `x`, `y` of a linear order is recorded as the sorted pair
`(min x y, max x y)`. This file collects facts about sorted pairs, their images under a function
and how two of them can overlap, and a comparison of the relative orders of two triples of distinct
points.

## Main results

* `TauCeti.min_max_comm`: the sorted pair of `x` and `y` does not depend on their order.
* `TauCeti.min_apply_min_max`, `TauCeti.max_apply_min_max`: applying a function to the sorted
  pair of `a` and `b` and sorting again gives the sorted pair of `f a` and `f b`.
* `TauCeti.min_max_share_coord`: two sorted pairs with a common point share a coordinate.
* `TauCeti.exists_min_max_of_share_coord`: two distinct increasing pairs sharing a coordinate are
  the sorted pairs `(min s u, max s u)` and `(min s w, max s w)` of three distinct points.
* `TauCeti.xor_of_lt_iff`: given triples `s, u, w` and `S, U, W` of distinct points in two linear
  orders with `s < u ↔ U < S` and `s < w ↔ W < U`, exactly one of two further pairs of order
  conditions holds.
-/

public section

namespace TauCeti

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- The sorted pair of `x` and `y` does not depend on their order. -/
theorem min_max_comm (x y : α) : (min x y, max x y) = (min y x, max y x) := by
  rw [min_comm, max_comm]

/-- The smaller of the values of `f` at the smaller and the larger of `a` and `b` is the smaller of
`f a` and `f b`. -/
theorem min_apply_min_max (f : α → β) (a b : α) :
    min (f (min a b)) (f (max a b)) = min (f a) (f b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, min_comm]

/-- The larger of the values of `f` at the smaller and the larger of `a` and `b` is the larger of
`f a` and `f b`. -/
theorem max_apply_min_max (f : α → β) (a b : α) :
    max (f (min a b)) (f (max a b)) = max (f a) (f b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, max_comm]

/-- Two sorted pairs with the common point `z` share a coordinate: some coordinate of
`(min y z, max y z)` is a coordinate of `(min x z, max x z)`. -/
theorem min_max_share_coord (x y z : α) :
    ¬(min y z ≠ min x z ∧ min y z ≠ max x z ∧ max y z ≠ min x z ∧ max y z ≠ max x z) := by
  rcases le_total x z with h₁ | h₁ <;> rcases le_total y z with h₂ | h₂ <;>
    simp [h₁, h₂]

/-- Two distinct increasing pairs `p` and `q` sharing a coordinate share exactly one point: they are
the sorted pairs `(min s u, max s u)` and `(min s w, max s w)` for distinct `s`, `u`, `w`. -/
theorem exists_min_max_of_share_coord {p q : α × α} (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hpq : p ≠ q) (h : ¬(q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2)) :
    ∃ s u w : α, s ≠ u ∧ s ≠ w ∧ u ≠ w ∧ p = (min s u, max s u) ∧ q = (min s w, max s w) := by
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  dsimp only at hp hq h
  have hp' : (p₁, p₂) = (min p₁ p₂, max p₁ p₂) := by rw [min_eq_left hp.le, max_eq_right hp.le]
  have hq' : (q₁, q₂) = (min q₁ q₂, max q₁ q₂) := by rw [min_eq_left hq.le, max_eq_right hq.le]
  by_cases h₁ : q₁ = p₁
  · subst h₁
    refine ⟨q₁, p₂, q₂, hp.ne, hq.ne, fun h ↦ hpq (by rw [h]), hp', hq'⟩
  by_cases h₂ : q₁ = p₂
  · subst h₂
    refine ⟨q₁, p₁, q₂, hp.ne', hq.ne, (hp.trans hq).ne, by rwa [min_comm, max_comm], hq'⟩
  by_cases h₃ : q₂ = p₁
  · subst h₃
    refine ⟨q₂, p₂, q₁, hp.ne, hq.ne', (hq.trans hp).ne', hp', by rwa [min_comm, max_comm]⟩
  have h₄ : q₂ = p₂ := by_contra fun h₄ ↦ h ⟨h₁, h₂, h₃, h₄⟩
  subst h₄
  refine ⟨q₂, p₁, q₁, hp.ne', hq.ne', fun h ↦ hpq (by rw [h]), by rwa [min_comm, max_comm],
    by rwa [min_comm, max_comm]⟩

/-- A comparison of the relative orders of two triples of distinct points `s, u, w` and `S, U, W`,
in possibly different linear orders. If `s < u ↔ U < S` and `s < w ↔ W < U`, then exactly one of
`(s < w ↔ W < S) ∧ (u < w ↔ S < U)` and `(u < w ↔ W < U) ∧ (s < u ↔ W < S)` holds.

When the strands of a strand diagram starting at `s`, `u`, `w` end at `S`, `U`, `W`, these are the
crossing conditions for the three ways of resolving two of their crossings in succession. -/
theorem xor_of_lt_iff {s u w : α} {S U W : β}
    (hsu : s ≠ u) (hsw : s ≠ w) (huw : u ≠ w) (hSU : S ≠ U) (hSW : S ≠ W) (hUW : U ≠ W)
    (h₁ : s < u ↔ U < S) (h₂ : s < w ↔ W < U) :
    Xor ((s < w ↔ W < S) ∧ (u < w ↔ S < U)) ((u < w ↔ W < U) ∧ (s < u ↔ W < S)) := by
  rcases lt_or_gt_of_ne hsu with h₃ | h₃ <;> rcases lt_or_gt_of_ne hsw with h₄ | h₄ <;>
    rcases lt_or_gt_of_ne huw with h₅ | h₅ <;> rcases lt_or_gt_of_ne hSU with h₆ | h₆ <;>
    rcases lt_or_gt_of_ne hSW with h₇ | h₇ <;> rcases lt_or_gt_of_ne hUW with h₈ | h₈ <;>
    simp only [xor_def, h₃, h₄, h₅, h₆, h₇, h₈, h₃.not_gt, h₄.not_gt, h₅.not_gt, h₆.not_gt,
      h₇.not_gt, h₈.not_gt, iff_true, iff_false, not_true_eq_false, not_false_eq_true, and_true,
      and_false, or_false, false_or] at h₁ h₂ ⊢ <;>
    order

end TauCeti
