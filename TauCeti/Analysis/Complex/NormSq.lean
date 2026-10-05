/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Circles centred on the real line

For two real points `c₁`, `c₂` of the complex plane, the difference of the two power functions
`|z - c|² - |C - c|²` is affine in the real part of `z` and vanishes when `z.re = C.re`
(`Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`): the radical axis of two circles centred on
the real line is the vertical line through their intersection points. This file also records the
real points of such a circle and on which side of a second circle its points lie.

## Main results

* `Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`: the radical-line identity.
* `Complex.norm_sub_eq_of_normSq_sub_eq`: a point at squared distance `ρ ^ 2` is at distance `ρ`.
* `Complex.eq_sub_of_normSq_eq_of_lt_re`, `Complex.eq_add_of_normSq_eq_of_re_lt`: a real point of
  the circle of centre `m` and radius `ρ` is `m - ρ` or `m + ρ`, according to its side.
* `Complex.lt_normSq_sub_of_normSq_eq`: points of one circle on one side of an intersection point
  with a second circle lie strictly outside the second circle.
* `Complex.re_mem_Icc_of_normSq_sub_eq`: the points of the circle of centre `m` and radius `ρ`
  have real part in `[m - ρ, m + ρ]`.
* `Complex.le_normSq_sub_of_le_normSq_sub`: points on or outside one circle, between two of its
  points that lie on or outside a second circle, lie on or outside the second circle.
-/

public section

namespace Complex

/-- The "radical line" identity: for real centres `c₁` and `c₂`, the difference of the two power
functions `|z - c|² - |C - c|²` of `z` is affine in `z.re` and vanishes at `C.re`. -/
theorem normSq_sub_ofReal_sub_normSq_sub_ofReal {c₁ c₂ : ℝ} (C z : ℂ) :
    (Complex.normSq (z - c₁) - Complex.normSq (C - c₁)) -
        (Complex.normSq (z - c₂) - Complex.normSq (C - c₂)) =
      2 * (c₂ - c₁) * (z.re - C.re) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  ring

/-- A point at squared distance `ρ ^ 2` from `m`, with `0 ≤ ρ`, is at distance `ρ`. -/
theorem norm_sub_eq_of_normSq_sub_eq {z : ℂ} {m ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : Complex.normSq (z - m) = ρ ^ 2) : ‖z - m‖ = ρ := by
  rwa [Complex.normSq_eq_norm_sq, pow_left_inj₀ (norm_nonneg _) hρ two_ne_zero] at h

/-- A real point `x` of the circle of centre `m` and radius `ρ`, to the left of a complex point
`w` of that circle, is its left endpoint `m - ρ`. -/
theorem eq_sub_of_normSq_eq_of_lt_re {x m ρ : ℝ} {w : ℂ} (hρ : 0 ≤ ρ)
    (hx : Complex.normSq ((x : ℂ) - m) = ρ ^ 2) (hw : Complex.normSq (w - m) = ρ ^ 2)
    (hxw : (x : ℂ).re < w.re) : x = m - ρ := by
  rw [← Complex.ofReal_sub, Complex.normSq_ofReal] at hx
  rw [Complex.normSq_apply] at hw
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hw hxw
  have hlt : x - m < ρ := by nlinarith [mul_self_nonneg w.im]
  have h : (x - m + ρ) * (x - m - ρ) = 0 := by linear_combination hx
  linarith [(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hlt.ne)]

/-- A real point `x` of the circle of centre `m` and radius `ρ`, to the right of a complex point
`w` of that circle, is its right endpoint `m + ρ`. -/
theorem eq_add_of_normSq_eq_of_re_lt {x m ρ : ℝ} {w : ℂ} (hρ : 0 ≤ ρ)
    (hx : Complex.normSq ((x : ℂ) - m) = ρ ^ 2) (hw : Complex.normSq (w - m) = ρ ^ 2)
    (hwx : w.re < (x : ℂ).re) : x = m + ρ := by
  rw [← Complex.ofReal_sub, Complex.normSq_ofReal] at hx
  rw [Complex.normSq_apply] at hw
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hw hwx
  have hlt : -ρ < x - m := by nlinarith [mul_self_nonneg w.im]
  have h : (x - m + ρ) * (x - m - ρ) = 0 := by linear_combination hx
  linarith [(mul_eq_zero.1 h).resolve_left (by linarith)]

/-- **The radical line of two circles.** Let `a` lie on two circles centred on the real axis, the
level sets `|· - m₁|² = r₁` and `|· - m₂|² = r₂`, and let `w` lie on the first, to the left of `a`
and strictly outside the second. Then every point `z` of the first circle to the left of `a` is
strictly outside the second: on the first circle, `|z - m₂|² - r₂` is an affine function of
`Re z`, vanishing at `a`. -/
theorem lt_normSq_sub_of_normSq_eq {a w z : ℂ} {m₁ r₁ m₂ r₂ : ℝ}
    (ha₁ : Complex.normSq (a - m₁) = r₁) (ha₂ : Complex.normSq (a - m₂) = r₂)
    (hw₁ : Complex.normSq (w - m₁) = r₁) (hw₂ : r₂ < Complex.normSq (w - m₂))
    (hz₁ : Complex.normSq (z - m₁) = r₁) (hwa : w.re < a.re) (hza : z.re < a.re) :
    r₂ < Complex.normSq (z - m₂) := by
  -- the radical-line identity, on the first circle, through `a`
  have hz := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m₁) (c₂ := m₂) a z
  have hw := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m₁) (c₂ := m₂) a w
  rw [hz₁, ha₁, ha₂] at hz
  rw [hw₁, ha₁, ha₂] at hw
  have hm : m₁ - m₂ < 0 := by nlinarith
  nlinarith

/-- A point at squared distance `ρ ^ 2` from the real point `m`, with `0 ≤ ρ`, has real part in
`[m - ρ, m + ρ]`. -/
theorem re_mem_Icc_of_normSq_sub_eq {w : ℂ} {m ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : Complex.normSq (w - m) = ρ ^ 2) : w.re ∈ Set.Icc (m - ρ) (m + ρ) := by
  have hre := Complex.abs_re_le_norm (w - m)
  rw [norm_sub_eq_of_normSq_sub_eq hρ h, Complex.sub_re, Complex.ofReal_re, abs_le] at hre
  constructor <;> linarith [hre.1, hre.2]

/-- Let `w₁`, `w₂` lie on the circle `|· - m|² = r` and on or outside the circle
`|· - m'|² = r'`, for real centres `m` and `m'`. Then every point `z` on or outside the first
circle with real part between those of `w₁` and `w₂` lies on or outside the second. -/
theorem le_normSq_sub_of_le_normSq_sub {w₁ w₂ z : ℂ} {m r m' r' : ℝ}
    (h₁ : Complex.normSq (w₁ - m) = r) (h₂ : Complex.normSq (w₂ - m) = r)
    (h₁' : r' ≤ Complex.normSq (w₁ - m')) (h₂' : r' ≤ Complex.normSq (w₂ - m'))
    (hz : r ≤ Complex.normSq (z - m)) (h₁z : w₁.re ≤ z.re) (hz₂ : z.re ≤ w₂.re) :
    r' ≤ Complex.normSq (z - m') := by
  have e₁ := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m') (c₂ := m) w₁ z
  have e₂ := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m') (c₂ := m) w₂ z
  rcases le_total 0 (m - m') with h | h
  · nlinarith [mul_nonneg h (sub_nonneg.2 h₁z)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos h (sub_nonpos.2 hz₂)]

end Complex
