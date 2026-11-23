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
(`Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`). Hence the radical axis of two circles centred
on the real line, the set of points with the same power with respect to both, is a vertical line
when the centres are distinct, and it contains every intersection point of the two circles. This
file also records on which side of a second circle the points of such a circle lie, and that a
real point of a circle centred at a real point `m` lies on the sphere of the same centre and
radius in `ℝ` (`Real.mem_sphere_of_normSq_sub_eq`).

## Main results

* `Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`: the radical-line identity.
* `Complex.norm_sq_add_I_mul_div_sqrt_two`: the squared norm of a normalized complex pair.
* `Complex.lt_normSq_sub_of_le_normSq_sub`: if the second of two circles has its centre to the
  right of the first, and the power of `a` with respect to the first is at most that with respect
  to the second, the points on or outside the first circle to the left of `a` lie strictly outside
  the second.
* `Complex.lt_normSq_sub_of_le_normSq_sub_of_sub_lt_sub`: the same, with the order of the centres
  witnessed by a point to the left of `a` at which the power with respect to the second circle
  minus that with respect to the first is larger than at `a`.
* `Complex.le_normSq_sub_of_le_normSq_sub`: points on or outside one circle, between two of its
  points that lie on or outside a second circle, lie on or outside the second circle.
* `Complex.norm_one_add_sq_div_sq_of_norm_eq`: on the circle `‖z‖ = R`, `‖1 + z² / R²‖` is
  `2 |re z| / R`.
* `Complex.sqrt_sq_add_sq_le_norm_add_mul_I`: a lower bound from a nonnegative real-coordinate
  margin at a fixed imaginary height.
-/

public section

namespace Complex

/-- The squared norm of a complex number with real part `x` and imaginary part `y`, divided by
`√2`, is `(x ^ 2 + y ^ 2) / 2`. -/
theorem norm_sq_add_I_mul_div_sqrt_two (x y : ℝ) :
    ‖((x : ℂ) + I * y) / (Real.sqrt 2 : ℝ)‖ ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
  rw [Complex.sq_norm, map_div₀, normSq_ofReal, mul_comm I,
    normSq_add_mul_I, Real.mul_self_sqrt (by norm_num)]

/-- The "radical line" identity: for real centres `c₁` and `c₂`, the difference of the two power
functions `|z - c|² - |C - c|²` of `z` is affine in `z.re` and vanishes at `C.re`. -/
theorem normSq_sub_ofReal_sub_normSq_sub_ofReal {c₁ c₂ : ℝ} (C z : ℂ) :
    (normSq (z - c₁) - normSq (C - c₁)) -
        (normSq (z - c₂) - normSq (C - c₂)) =
      2 * (c₂ - c₁) * (z.re - C.re) := by
  simp only [normSq_apply, sub_re, sub_im, ofReal_re,
    ofReal_im, sub_zero]
  ring

/-- **The radical line of two circles.** Consider two circles centred on the real axis, the level
sets `|· - m₁|² = r₁` and `|· - m₂|² = r₂`, with `m₁ < m₂`, and a point `a` whose power
`|a - m₁|² - r₁` with respect to the first is at most its power with respect to the second. Then
every point `z` on or outside the first circle to the left of `a` is strictly outside the second:
the power with respect to the second circle minus the power with respect to the first grows by
`2 (m₂ - m₁) (Re a - Re z)` from `a` to `z`. -/
theorem lt_normSq_sub_of_le_normSq_sub (z : ℂ) {a : ℂ} {m₁ r₁ m₂ r₂ : ℝ}
    (ha : normSq (a - m₁) - r₁ ≤ normSq (a - m₂) - r₂) (hm : m₁ < m₂)
    (hz₁ : r₁ ≤ normSq (z - m₁)) (hza : z.re < a.re) :
    r₂ < normSq (z - m₂) := by
  have hz := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m₁) (c₂ := m₂) a z
  nlinarith [mul_pos (sub_pos.2 hm) (sub_pos.2 hza)]

/-- **The radical line of two circles, with a witness.** Consider two circles centred on the real
axis, the level sets `|· - m₁|² = r₁` and `|· - m₂|² = r₂`, and a point `a` whose power with
respect to the first is at most that with respect to the second. Let `w`, to the left of `a`, be a
point at which the power with respect to the second circle minus the power with respect to the
first is larger than at `a`; equivalently, from `a` to `w` the signed change in the squared
distance to `m₂` is greater than the signed change in the squared distance to `m₁` (both changes
may be negative). Then every point `z` on or outside the first circle to the left of `a` is
strictly outside the second. -/
theorem lt_normSq_sub_of_le_normSq_sub_of_sub_lt_sub (z : ℂ) {a w : ℂ} {m₁ r₁ m₂ r₂ : ℝ}
    (ha : normSq (a - m₁) - r₁ ≤ normSq (a - m₂) - r₂)
    (hw : normSq (w - m₁) - normSq (a - m₁) < normSq (w - m₂) - normSq (a - m₂))
    (hz₁ : r₁ ≤ normSq (z - m₁)) (hwa : w.re < a.re) (hza : z.re < a.re) :
    r₂ < normSq (z - m₂) := by
  -- the second centre lies to the right of the first: the second power minus the first grows by
  -- `2 (m₂ - m₁) (Re a - Re w)` from `a` to `w`, to its left
  have hd := normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := m₁) (c₂ := m₂) a w
  have hm : m₁ < m₂ := by nlinarith
  exact lt_normSq_sub_of_le_normSq_sub z ha hm hz₁ hza

/-- Let `w₁`, `w₂` lie on the circle `|· - m|² = r` and on or outside the circle
`|· - m'|² = r'`, for real centres `m` and `m'`. Then every point `z` on or outside the first
circle with real part between those of `w₁` and `w₂` lies on or outside the second. -/
theorem le_normSq_sub_of_le_normSq_sub {w₁ w₂ z : ℂ} {m r m' r' : ℝ}
    (h₁ : normSq (w₁ - m) = r) (h₂ : normSq (w₂ - m) = r)
    (h₁' : r' ≤ normSq (w₁ - m')) (h₂' : r' ≤ normSq (w₂ - m'))
    (hz : r ≤ normSq (z - m)) (h₁z : w₁.re ≤ z.re) (hz₂ : z.re ≤ w₂.re) :
    r' ≤ normSq (z - m') := by
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

/-- A nonnegative lower bound for the absolute real coordinate gives a Euclidean lower bound
for a complex point at the same imaginary height. -/
theorem sqrt_sq_add_sq_le_norm_add_mul_I {a c t : ℝ} (ha : 0 ≤ a) (hac : a ≤ |c|) :
    Real.sqrt (a ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ := by
  apply (Real.sqrt_le_left (norm_nonneg _)).mpr
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith only [ha, hac, sq_abs c]

end Complex

namespace Real

/-- A real point `x` on the circle of centre `m` and radius `ρ ≥ 0` in `ℂ` lies on the sphere of
centre `m` and radius `ρ` in `ℝ`, since the inclusion `ℝ → ℂ` is an isometry. -/
theorem mem_sphere_of_normSq_sub_eq (x : ℝ) {m ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : Complex.normSq ((x : ℂ) - m) = ρ ^ 2) : x ∈ Metric.sphere m ρ := by
  rw [Metric.mem_sphere, ← Complex.isometry_ofReal.dist_eq, dist_eq_norm, Complex.norm_def, h,
    Real.sqrt_sq hρ]

end Real
