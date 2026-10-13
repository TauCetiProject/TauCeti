/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Ratios of sines and of hyperbolic sines at proportional arguments

For a fixed `t ∈ [0, 1]` this file compares `sin (t * a)` with `sin a` and `sinh (t * b)` with
`sinh b`. The sine is concave on `[0, π]` and the hyperbolic sine is convex on `[0, ∞)`, so
`t * sin a ≤ sin (t * a)` for `a ∈ [0, π]` and `sinh (t * b) ≤ t * sinh b` for `b ≥ 0`.
Moreover the ratio `sin (t * a) / sin a` increases with `a` on `(0, π)`, while
`sinh (t * b) / sinh b` decreases with `b` on `(0, ∞)`.

These ratios are the distortion coefficients of the model spaces of constant curvature: up to
rescaling, `sin (t * a) / sin a` compares the Jacobi field along a geodesic of a sphere at time `t`
with its value at time `1`, and `sinh (t * b) / sinh b` does the same in hyperbolic space. The
monotonicity statements say that these comparisons grow with the curvature.

## Main statements

* `Real.strictConvexOn_sinh_Ici`: `sinh` is strictly convex on `[0, ∞)`.
* `Real.mul_sin_le_sin_mul`: `t * sin a ≤ sin (t * a)` for `t ∈ [0, 1]` and `a ∈ [0, π]`.
* `Real.sinh_mul_le_mul_sinh`: `sinh (t * b) ≤ t * sinh b` for `t ∈ [0, 1]` and `b ≥ 0`.
* `Real.monotoneOn_sin_mul_div_sin`: `a ↦ sin (t * a) / sin a` is monotone on `(0, π)`.
* `Real.antitoneOn_sinh_mul_div_sinh`: `b ↦ sinh (t * b) / sinh b` is antitone on `(0, ∞)`.
-/

public section

open Set

namespace Real

/-- The hyperbolic sine is strictly convex on `[0, ∞)`. -/
theorem strictConvexOn_sinh_Ici : StrictConvexOn ℝ (Ici 0) sinh := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) continuous_sinh.continuousOn ?_
  rw [interior_Ici, deriv_sinh]
  intro x hx y hy hxy
  rw [mem_Ioi] at hx hy
  exact cosh_lt_cosh.2 (by rwa [abs_of_pos hx, abs_of_pos hy])

/-- For `t ∈ [0, 1]` and `a ∈ [0, π]`, `t * sin a ≤ sin (t * a)`. -/
theorem mul_sin_le_sin_mul {t a : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (ha₀ : 0 ≤ a) (ha : a ≤ π) :
    t * sin a ≤ sin (t * a) := by
  simpa using strictConcaveOn_sin_Icc.concaveOn.2 ⟨ha₀, ha⟩ ⟨le_rfl, pi_pos.le⟩ ht₀
    (sub_nonneg.2 ht₁) (add_sub_cancel t 1)

/-- For `t ∈ [0, 1]` and `b ≥ 0`, `sinh (t * b) ≤ t * sinh b`. -/
theorem sinh_mul_le_mul_sinh {t b : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hb : 0 ≤ b) :
    sinh (t * b) ≤ t * sinh b := by
  simpa using strictConvexOn_sinh_Ici.convexOn.2 (mem_Ici.2 hb) (mem_Ici.2 le_rfl) ht₀
    (sub_nonneg.2 ht₁) (add_sub_cancel t 1)

/-- The numerator of the derivative of `a ↦ sin (t * a) / sin a` is nonnegative on `[0, π]`.
The difference `t * cos (t * a) * sin a - sin (t * a) * cos a` vanishes at `0` and has derivative
`(1 - t ^ 2) * sin (t * a) * sin a ≥ 0`. -/
private theorem sin_mul_mul_cos_le {t a : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (ha₀ : 0 ≤ a)
    (ha : a ≤ π) : sin (t * a) * cos a ≤ t * cos (t * a) * sin a := by
  set h : ℝ → ℝ := fun x ↦ t * cos (t * x) * sin x - sin (t * x) * cos x
  have hd : ∀ x, HasDerivAt h ((1 - t ^ 2) * sin (t * x) * sin x) x := by
    intro x
    have hc : HasDerivAt (fun x ↦ t * x) t x := by simpa using (hasDerivAt_id x).const_mul t
    convert ((hc.cos.const_mul t).mul (hasDerivAt_sin x)).sub (hc.sin.mul (hasDerivAt_cos x))
      using 1
    ring
  have hmono : MonotoneOn h (Icc 0 π) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 π)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt) (fun x _ ↦ (hd x).differentiableAt
        |>.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have htx : t * x ≤ π := (mul_le_of_le_one_left hx.1.le ht₁).trans hx.2.le
    exact mul_nonneg (mul_nonneg (by nlinarith) (sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg ht₀ hx.1.le) htx)) (sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le)
  have := hmono ⟨le_rfl, pi_pos.le⟩ ⟨ha₀, ha⟩ ha₀
  simp only [h, mul_zero, sin_zero, cos_zero, mul_one, sub_zero] at this
  linarith

/-- The numerator of the derivative of `b ↦ sinh (t * b) / sinh b` is nonpositive on `[0, ∞)`.
The difference `sinh (t * b) * cosh b - t * cosh (t * b) * sinh b` vanishes at `0` and has
derivative `(1 - t ^ 2) * sinh (t * b) * sinh b ≥ 0`. -/
private theorem mul_cosh_mul_sinh_le {t b : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hb : 0 ≤ b) :
    t * cosh (t * b) * sinh b ≤ sinh (t * b) * cosh b := by
  set h : ℝ → ℝ := fun x ↦ sinh (t * x) * cosh x - t * cosh (t * x) * sinh x
  have hd : ∀ x, HasDerivAt h ((1 - t ^ 2) * sinh (t * x) * sinh x) x := by
    intro x
    have hc : HasDerivAt (fun x ↦ t * x) t x := by simpa using (hasDerivAt_id x).const_mul t
    convert (hc.sinh.mul (hasDerivAt_cosh x)).sub ((hc.cosh.const_mul t).mul (hasDerivAt_sinh x))
      using 1
    ring
  have hmono : MonotoneOn h (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt) (fun x _ ↦ (hd x).differentiableAt
        |>.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Ici, mem_Ioi] at hx
    rw [(hd x).deriv]
    exact mul_nonneg (mul_nonneg (by nlinarith) (sinh_nonneg_iff.2 (mul_nonneg ht₀ hx.le)))
      (sinh_nonneg_iff.2 hx.le)
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hb) hb
  simp only [h, mul_zero, sinh_zero, cosh_zero, mul_one, sub_zero] at this
  linarith

/-- For `t ∈ [0, 1]`, the ratio `sin (t * a) / sin a` is monotone in `a` on `(0, π)`. -/
theorem monotoneOn_sin_mul_div_sin {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    MonotoneOn (fun a ↦ sin (t * a) / sin a) (Ioo 0 π) := by
  have hc : ∀ x, HasDerivAt (fun x ↦ t * x) t x := fun x ↦ by
    simpa using (hasDerivAt_id x).const_mul t
  have hd : ∀ x ∈ Ioo 0 π, HasDerivAt (fun a ↦ sin (t * a) / sin a)
      ((cos (t * x) * t * sin x - sin (t * x) * cos x) / sin x ^ 2) x := fun x hx ↦
    ((hc x).sin.div (hasDerivAt_sin x) (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne')
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 π)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · rw [interior_Ioo] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo] at hx
    rw [(hd x hx).deriv]
    refine div_nonneg ?_ (sq_nonneg _)
    nlinarith [sin_mul_mul_cos_le ht₀ ht₁ hx.1.le hx.2.le]

/-- For `t ∈ [0, 1]`, the ratio `sinh (t * b) / sinh b` is antitone in `b` on `(0, ∞)`. -/
theorem antitoneOn_sinh_mul_div_sinh {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    AntitoneOn (fun b ↦ sinh (t * b) / sinh b) (Ioi 0) := by
  have hc : ∀ x, HasDerivAt (fun x ↦ t * x) t x := fun x ↦ by
    simpa using (hasDerivAt_id x).const_mul t
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun b ↦ sinh (t * b) / sinh b)
      ((cosh (t * x) * t * sinh x - sinh (t * x) * cosh x) / sinh x ^ 2) x := fun x hx ↦
    ((hc x).sinh.div (hasDerivAt_sinh x) (sinh_pos_iff.2 hx).ne')
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hx
    rw [(hd x hx).deriv]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    nlinarith [mul_cosh_mul_sinh_le ht₀ ht₁ (le_of_lt hx)]

end Real
