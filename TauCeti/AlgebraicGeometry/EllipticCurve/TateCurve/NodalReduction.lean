/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Points with `‖x‖ = 1` on equations reducing to the nodal cubic

Let `K` be an ultrametric normed field and `A₄, A₆ ∈ K` with `‖A₄‖, ‖A₆‖ < 1`. Modulo the maximal
ideal, the equation `y² + xy = x³ + A₄x + A₆` (the shape of the Tate curve) is the nodal cubic
`y² + xy = x³`. This file records two facts about its solutions with `‖x‖ = 1`, which reduce to
nonsingular points of the nodal cubic other than the point at infinity: both tangent directions
`y` and `x + y` at the node are units, and a line through the origin meets the curve in at most
one such solution. No completeness, discreteness or characteristic assumption is needed.

## Main results

* `TauCeti.norm_eq_one_and_norm_add_eq_one_of_equation`: a solution with `‖x‖ = 1` has
  `‖y‖ = ‖x + y‖ = 1`.
* `TauCeti.eq_and_eq_of_mul_eq_mul_of_equation`: two solutions with first coordinates of norm one
  on a common line through the origin are equal.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- On a curve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ < 1`, a solution with `‖x‖ = 1` has
`‖y‖ = ‖x + y‖ = 1`. -/
theorem norm_eq_one_and_norm_add_eq_one_of_equation {A₄ A₆ x y : K} (hA₄ : ‖A₄‖ < 1)
    (hA₆ : ‖A₆‖ < 1) (hx : ‖x‖ = 1) (h : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆) :
    ‖y‖ = 1 ∧ ‖x + y‖ = 1 := by
  have hr : ‖x ^ 3 + A₄ * x + A₆‖ = 1 := by
    have hx3 : ‖x ^ 3‖ = 1 := by rw [norm_pow, hx, one_pow]
    rw [← hx3, add_assoc]
    refine (IsUltrametricDist.norm_eq_of_norm_sub_lt_left ?_).symm
    rw [sub_add_cancel_left, norm_neg, hx3]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hA₆)
    rwa [norm_mul, hx, mul_one]
  have hp : ‖y‖ * ‖x + y‖ = 1 := by
    rw [← norm_mul, ← hr, ← h]
    ring_nf
  have hs : ‖x + y‖ ≤ max 1 ‖y‖ := hx ▸ IsUltrametricDist.norm_add_le_max x y
  rcases le_or_gt ‖y‖ 1 with hy | hy
  · have hs' : ‖x + y‖ ≤ 1 := hs.trans (max_le le_rfl hy)
    constructor <;> nlinarith [norm_nonneg y, norm_nonneg (x + y)]
  · have he : ‖x + y‖ = ‖y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne), hx,
        max_eq_right hy.le]
    rw [he] at hp
    nlinarith

/-- **A line through the origin meets the curve in at most one point with `‖x‖ = 1`.** If
`(x, y)` and `(X, Y)` solve `y² + xy = x³ + A₄x + A₆` with `‖A₄‖, ‖A₆‖ < 1`, both first coordinates
have norm one and `x Y = y X`, then the two points are equal. -/
theorem eq_and_eq_of_mul_eq_mul_of_equation {A₄ A₆ x y X Y : K} (hA₄ : ‖A₄‖ < 1)
    (hA₆ : ‖A₆‖ < 1) (hx : ‖x‖ = 1) (hX : ‖X‖ = 1) (h₁ : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆)
    (h₂ : Y ^ 2 + X * Y = X ^ 3 + A₄ * X + A₆) (h : x * Y = y * X) : X = x ∧ Y = y := by
  have key : (x - X) * (x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X))) = 0 := by
    linear_combination x ^ 2 * h₂ - X ^ 2 * h₁ - (x * Y + y * X + x * X) * h
  have h₀ : ‖x ^ 2 * X ^ 2‖ = 1 := by rw [norm_mul, norm_pow, norm_pow, hx, hX]; simp
  have hne : x ^ 2 * X ^ 2 - (A₄ * x * X + A₆ * (x + X)) ≠ 0 := by
    rw [← norm_ne_zero_iff, ← (IsUltrametricDist.norm_eq_of_norm_sub_lt_left _), h₀]
    · exact one_ne_zero
    rw [sub_sub_cancel, h₀]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rwa [norm_mul, norm_mul, hx, hX, mul_one, mul_one]
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        ((IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hx, hX, max_self]))).trans_lt hA₆
  have hxX : X = x := (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)).symm
  refine ⟨hxX, ?_⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  rw [hxX, mul_comm y] at h
  exact mul_left_cancel₀ hx0 h

end TauCeti
