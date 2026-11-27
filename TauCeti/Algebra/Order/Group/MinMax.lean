/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.Interval.Set.Defs

/-!
# Clamping and medians in ordered additive groups

In a linearly ordered additive group, clamping to a symmetric interval is bounded by its
height and does not increase absolute value. Clamping `t` to `[0, a + b]`, for `0 ≤ a` and
`0 ≤ b`, is the sum of clamping `t` to `[0, a]` and clamping the remaining time `t - a` to
`[0, b]`. This is how a constant-speed run along a segment of duration `a + b` splits into its
runs along the two pieces of durations `a` and `b`.

The median `max 0 (min a b) + min 0 (max a b)` of `0`, `a` and `b` is the common initial segment
of `a` and `b`, viewed as segments from `0` on the line: it lies between `0` and each of them, and
twice its absolute value is `|a| + |b| - |b - a|`.

Moreover, for `a ≤ b` in a linear order and a function `f` monotone on `[a, b]` into an ordered
additive group, the clipped increment `t ↦ f (min b t) - f (min a t)` is monotone
(`MonotoneOn.min_sub_min`, `Monotone.min_sub_min`).

## Main results

* `TauCeti.max_zero_min_add`: `max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b)`.
* `TauCeti.abs_max_min_le`: the max-min clipping formula is bounded by `|M|` for any height `M`.
* `TauCeti.abs_max_min_le_abs`: clipping at a nonnegative height does not increase absolute value.
* `TauCeti.max_neg_min_eq_self_of_abs_le`: clipping fixes elements in the symmetric interval.
* `TauCeti.add_max_neg_min_nonneg`: clamping two elements with nonnegative sum to `[-r, r]` leaves
  a nonnegative sum.
* `TauCeti.abs_max_zero_min_add_min_zero_max_add_abs_sub`: the median `u` of `0`, `a` and `b`
  satisfies `|u| + |a - u| = |a|`.
* `TauCeti.two_nsmul_abs_max_zero_min_add_min_zero_max`: `2 • |u| = |a| + |b| - |b - a|`.
* `MonotoneOn.min_sub_min`, `Monotone.min_sub_min`: the clipped increment
  `t ↦ f (min b t) - f (min a t)` of a monotone function is monotone.
-/

public section

/-- For `a ≤ b` in a linear order and a function `f` monotone on `[a, b]` into an ordered additive
group, the clipped increment `t ↦ f (min b t) - f (min a t)` is monotone. -/
theorem MonotoneOn.min_sub_min {ι β : Type*} [LinearOrder ι] [AddGroup β] [Preorder β]
    [AddRightMono β] {f : ι → β} {a b : ι} (hf : MonotoneOn f (Set.Icc a b)) (hab : a ≤ b) :
    Monotone fun t ↦ f (min b t) - f (min a t) := fun s t hst ↦ by
  rcases le_total t a with hta | hat
  · simp [min_eq_right (hst.trans hta), min_eq_right ((hst.trans hta).trans hab),
      min_eq_right hta, min_eq_right (hta.trans hab)]
  · rcases le_total s a with hsa | has
    · simp only [min_eq_right hsa, min_eq_right (hsa.trans hab), sub_self,
        min_eq_left hat, sub_nonneg]
      exact hf ⟨le_rfl, hab⟩ ⟨le_min hab hat, min_le_left _ _⟩ (le_min hab hat)
    · simp only [min_eq_left has, min_eq_left hat]
      exact sub_le_sub_right
        (hf ⟨le_min hab has, min_le_left _ _⟩ ⟨le_min hab hat, min_le_left _ _⟩
          (min_le_min_left b hst)) _

/-- For `a ≤ b` in a linear order and a monotone function `f` into an ordered additive group, the
clipped increment `t ↦ f (min b t) - f (min a t)` is monotone. -/
theorem Monotone.min_sub_min {ι β : Type*} [LinearOrder ι] [AddGroup β] [Preorder β]
    [AddRightMono β] {f : ι → β} (hf : Monotone f) {a b : ι} (hab : a ≤ b) :
    Monotone fun t ↦ f (min b t) - f (min a t) :=
  (hf.monotoneOn _).min_sub_min hab

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Clamping `t` to `[0, a + b]` is the sum of clamping `t` to `[0, a]` and clamping the remaining
time `t - a` to `[0, b]`. -/
theorem max_zero_min_add {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : α) :
    max 0 (min t (a + b)) = max 0 (min t a) + max 0 (min (t - a) b) := by
  grind

/-- The max-min clipping formula is bounded by the absolute value of its height,
including when the height is negative. -/
theorem abs_max_min_le (M x : α) : |max (-M) (min M x)| ≤ |M| := by
  rw [abs_le]
  constructor <;> grind [le_abs_self, neg_abs_le]

/-- Clipping to a symmetric interval does not increase absolute value. -/
theorem abs_max_min_le_abs {M : α} (hM : 0 ≤ M) (x : α) :
    |max (-M) (min M x)| ≤ |x| := by
  rw [abs_le]
  constructor <;> grind [le_abs_self, neg_abs_le]

/-- Clipping to a symmetric interval fixes every element whose absolute value is at most
its height. -/
@[simp]
theorem max_neg_min_eq_self_of_abs_le {M x : α} (h : |x| ≤ M) :
    max (-M) (min M x) = x := by
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

/-- Clamping two elements with nonnegative sum to `[-r, r]` leaves a nonnegative sum. -/
theorem add_max_neg_min_nonneg {r a b : α} (h : 0 ≤ a + b) :
    0 ≤ max (-r) (min a r) + max (-r) (min b r) := by
  grind

/-- The median `u = max 0 (min a b) + min 0 (max a b)` of `0`, `a` and `b` lies between `0` and
`a`: `|u| + |a - u| = |a|`. -/
theorem abs_max_zero_min_add_min_zero_max_add_abs_sub (a b : α) :
    |max 0 (min a b) + min 0 (max a b)| + |a - (max 0 (min a b) + min 0 (max a b))| = |a| := by
  rcases le_total a b with hab | hab <;> rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, ha, hb] <;>
    grind [abs_of_nonneg, abs_of_nonpos]

/-- Twice the absolute value of the median `u = max 0 (min a b) + min 0 (max a b)` of `0`, `a`
and `b` is `|a| + |b| - |b - a|`: `u` is the common initial segment of `a` and `b`. -/
theorem two_nsmul_abs_max_zero_min_add_min_zero_max (a b : α) :
    2 • |max 0 (min a b) + min 0 (max a b)| = |a| + |b| - |b - a| := by
  rw [two_nsmul]
  rcases le_total a b with hab | hab <;> rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, ha, hb] <;>
    grind [abs_of_nonneg, abs_of_nonpos]

end TauCeti
