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
real points of such a circle and on which side of a second circle its points lie. It also bounds
the norm along upward vertical rays leaving a point of the closed upper half-plane.

## Main results

* `Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`: the radical-line identity.
* `Complex.norm_sq_add_I_mul_div_sqrt_two`: the squared norm of a normalized complex pair.
* `Complex.norm_sub_eq_of_normSq_sub_eq`: a point at squared distance `ρ ^ 2` is at distance `ρ`.
* `Complex.eq_sub_of_normSq_eq_of_lt_re`, `Complex.eq_add_of_normSq_eq_of_re_lt`: a real point of
  the circle of centre `m` and radius `ρ` is `m - ρ` or `m + ρ`, according to its side.
* `Complex.lt_normSq_sub_of_normSq_eq`: points of one circle on one side of an intersection point
  with a second circle lie strictly outside the second circle.
* `Complex.re_mem_Icc_of_normSq_sub_eq`: the points of the circle of centre `m` and radius `ρ`
  have real part in `[m - ρ, m + ρ]`.
* `Complex.le_normSq_sub_of_le_normSq_sub`: points on or outside one circle, between two of its
  points that lie on or outside a second circle, lie on or outside the second circle.
* `Complex.norm_one_add_sq_div_sq_of_norm_eq`: on the circle `‖z‖ = R`, `‖1 + z² / R²‖` is
  `2 |re z| / R`.
* `Complex.norm_le_norm_add_ofReal_mul_I`: for `0 ≤ z.im` and `0 ≤ s`, `‖z‖ ≤ ‖z + s * I‖`.
* `Complex.norm_add_div_two_le_norm_add_ofReal_mul_I`: for `0 ≤ z.im` and `0 ≤ s`,
  `(‖z‖ + s) / 2 ≤ ‖z + s * I‖`.
-/

public section

namespace Complex

/-- The squared norm of a complex number with real part `x` and imaginary part `y`, divided by
`√2`, is `(x ^ 2 + y ^ 2) / 2`. -/
theorem norm_sq_add_I_mul_div_sqrt_two (x y : ℝ) :
    ‖((x : ℂ) + Complex.I * y) / (Real.sqrt 2 : ℝ)‖ ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
  rw [Complex.sq_norm, map_div₀, Complex.normSq_ofReal, mul_comm Complex.I,
    Complex.normSq_add_mul_I, Real.mul_self_sqrt (by norm_num)]

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
  have _ : m₁ - m₂ < 0 := by nlinarith
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

/-- On the circle `‖z‖ = R`, the factor `1 + z² / R²` has modulus `2 |re z| / R`. This is
the cancellation behind the kernel of Newman's contour argument. -/
theorem norm_one_add_sq_div_sq_of_norm_eq {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ = 2 * |z.re| / R := by
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  -- On the circle `R² = z * conj z`, so `R² + z² = z * (conj z + z) = z * 2 re z`.
  have hR2 : (R : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [mul_conj, normSq_eq_norm_sq, hz]; push_cast; ring
  have hkey : 1 + z ^ 2 / (R : ℂ) ^ 2 = z * (z + (starRingEnd ℂ) z) / (R : ℂ) ^ 2 := by
    field_simp
    rw [hR2]
    ring
  rw [hkey, add_conj]
  simp only [norm_div, norm_mul, norm_pow, hz, norm_real, Real.norm_eq_abs,
    abs_two, abs_of_pos hR]
  field_simp

/-- For `z` in the closed upper half-plane, every point `z + s * I` (`s ≥ 0`) of the vertical ray
going upward from `z` is at least as far from the origin as `z`. -/
theorem norm_le_norm_add_ofReal_mul_I {z : ℂ} (hz : 0 ≤ z.im) {s : ℝ} (hs : 0 ≤ s) :
    ‖z‖ ≤ ‖z + (s : ℂ) * Complex.I‖ := by
  have hsq : ‖z‖ ^ 2 ≤ ‖z + (s : ℂ) * Complex.I‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    nlinarith
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- The points of a vertical ray leaving a point `z` of the closed upper half-plane upward, at
height `s` above `z`, are at distance at least `(‖z‖ + s) / 2` from the origin. -/
theorem norm_add_div_two_le_norm_add_ofReal_mul_I {z : ℂ} (hz : 0 ≤ z.im) {s : ℝ}
    (hs : 0 ≤ s) : (‖z‖ + s) / 2 ≤ ‖z + (s : ℂ) * Complex.I‖ := by
  have h1 := norm_le_norm_add_ofReal_mul_I hz hs
  have h2 : s ≤ ‖z + (s : ℂ) * Complex.I‖ := by
    refine le_trans ?_ (le_trans (le_abs_self _) (abs_im_le_norm (z + (s : ℂ) * Complex.I)))
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  linarith

end Complex
