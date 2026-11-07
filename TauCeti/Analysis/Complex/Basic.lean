/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation-invariant discs

Complex conjugation is an isometry fixing the real axis (Mathlib's `Complex.dist_conj_conj`), so
it maps every open or closed disc centred on the real axis to itself. Such discs are the natural
domains for reflection across the real axis, for instance the even reflection
`TauCeti.evenReflection`.

The file also records the coordinates, in the frame of a nonzero direction `v`, of the points
`v (s ± h i) + z₀` on the two sides of the line through `v s + z₀` with direction `v`: their
imaginary parts in that frame and their distance from `v s + z₀`.
-/

public section

namespace TauCeti

open ComplexConjugate Metric

variable {x₀ z : ℂ} {r : ℝ}

/-- Conjugation maps an open disc centred on the real axis to itself. -/
theorem conj_mem_ball_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ ball x₀ r) :
    conj z ∈ ball x₀ r := by
  rwa [mem_ball, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Conjugation maps a closed disc centred on the real axis to itself. -/
theorem conj_mem_closedBall_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ closedBall x₀ r) :
    conj z ∈ closedBall x₀ r := by
  rwa [mem_closedBall, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

section LineThrough

open Complex

variable {v z₀ : ℂ} {s : ℝ}

theorem im_div_add_mul_I_sub (hv : v ≠ 0) (h : ℝ) :
    ((v * (s + h * I) + z₀ - (v * s + z₀)) / v).im = h := by
  have : (v * (s + h * I) + z₀ - (v * s + z₀)) / v = h * I := by
    field_simp
    ring
  rw [this]
  simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]

theorem im_div_sub_mul_I_sub (hv : v ≠ 0) (h : ℝ) :
    ((v * (s - h * I) + z₀ - (v * s + z₀)) / v).im = -h := by
  have key : (v * (s - h * I) + z₀ - (v * s + z₀)) / v = -(h * I) := by
    field_simp
    ring
  simp only [key, neg_im, mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]

theorem dist_add_mul_I (h : ℝ) :
    dist (v * (s + h * I) + z₀) (v * s + z₀) = ‖v‖ * |h| := by
  rw [dist_eq_norm]
  have : v * (s + h * I) + z₀ - (v * s + z₀) = v * (h * I) := by ring
  rw [this, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem dist_sub_mul_I (h : ℝ) :
    dist (v * (s - h * I) + z₀) (v * s + z₀) = ‖v‖ * |h| := by
  rw [dist_eq_norm]
  have : v * (s - h * I) + z₀ - (v * s + z₀) = -(v * (h * I)) := by ring
  rw [this, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

end LineThrough

end TauCeti
