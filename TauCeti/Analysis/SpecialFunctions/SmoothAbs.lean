/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Real.Sqrt

/-!
# A smooth approximation of the absolute value

For a real parameter `η`, the function `TauCeti.smoothAbs η : t ↦ √(t ^ 2 + η ^ 2) - η` is the
absolute value for `η = 0` and is smooth for `η ≠ 0`, with derivative `t / √(t ^ 2 + η ^ 2)` of
absolute value at most `1`. For `η ≥ 0` it vanishes at `0`, lies between `0` and `|t|`, and is
within `η` of `|t|`.

Composing a smooth function `u` with `smoothAbs η` for `η > 0` gives smooth functions converging
uniformly to `|u|` as `η → 0⁺`, with pointwise gradients
`|∇(smoothAbs η ∘ u)| ≤ |∇u|`. This shows that `|u|` lies in a Sobolev space defined as a
completion of smooth functions, with no larger energy than `u`.

## Main declarations

* `TauCeti.smoothAbs`: the function `t ↦ √(t ^ 2 + η ^ 2) - η`.
* `TauCeti.contDiff_smoothAbs`, `TauCeti.hasDerivAt_smoothAbs`: its smoothness and derivative for
  `η ≠ 0`.
* `TauCeti.abs_deriv_smoothAbs_le_one`, `TauCeti.lipschitzWith_smoothAbs`: derivative and
  Lipschitz bounds by `1`.
* `TauCeti.abs_smoothAbs_sub_abs_le`: `smoothAbs η` is within `η` of the absolute value for `η ≥ 0`.
-/

public section

noncomputable section

namespace TauCeti

/-- The function `t ↦ √(t ^ 2 + η ^ 2) - η`, a smooth approximation of `|t|` for small `η ≠ 0`. -/
def smoothAbs (η t : ℝ) : ℝ := √(t ^ 2 + η ^ 2) - η

theorem smoothAbs_def (η t : ℝ) : smoothAbs η t = √(t ^ 2 + η ^ 2) - η := by
  rw [smoothAbs]

/-- At parameter zero, the approximation is exactly the absolute value. -/
@[simp]
theorem smoothAbs_zero_left (t : ℝ) : smoothAbs 0 t = |t| := by
  simp [smoothAbs, Real.sqrt_sq_eq_abs]

/-- For a nonnegative parameter, the approximation vanishes at zero. -/
@[simp]
theorem smoothAbs_zero_right {η : ℝ} (hη : 0 ≤ η) : smoothAbs η 0 = 0 := by
  simp [smoothAbs, Real.sqrt_sq hη]

/-- For `η ≠ 0`, `smoothAbs η` is `C^n` for every order, including `∞` and `ω`. -/
@[fun_prop]
theorem contDiff_smoothAbs {η : ℝ} (hη : η ≠ 0) {n : WithTop ℕ∞} : ContDiff ℝ n (smoothAbs η) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t ↦ by positivity) |>.sub contDiff_const

/-- For `η ≠ 0`, the derivative of `smoothAbs η` at `t` is `t / √(t² + η²)`. -/
theorem hasDerivAt_smoothAbs {η : ℝ} (hη : η ≠ 0) (t : ℝ) :
    HasDerivAt (smoothAbs η) (t / √(t ^ 2 + η ^ 2)) t := by
  have h := (Real.hasDerivAt_sqrt_sq_add (p := η ^ 2) t (by positivity)).sub_const η
  convert h using 1
  ext x
  rw [smoothAbs]

/-- For `η ≠ 0`, the derivative of the approximation has its explicit quotient formula. -/
@[simp]
theorem deriv_smoothAbs {η : ℝ} (hη : η ≠ 0) (t : ℝ) :
    deriv (smoothAbs η) t = t / √(t ^ 2 + η ^ 2) :=
  (hasDerivAt_smoothAbs hη t).deriv

/-- For every parameter, `smoothAbs η` is continuous, including at parameter zero. -/
@[fun_prop]
theorem continuous_smoothAbs (η : ℝ) : Continuous (smoothAbs η) :=
  ((continuous_id.pow 2).add continuous_const).sqrt.sub continuous_const

/-- The approximation is `1`-Lipschitz for every parameter. -/
theorem lipschitzWith_smoothAbs (η : ℝ) : LipschitzWith 1 (smoothAbs η) := by
  by_cases hη : η = 0
  · subst η
    have hzero : smoothAbs 0 = (norm : ℝ → ℝ) := by
      ext x
      simp
    rw [hzero]
    exact lipschitzWith_one_norm
  · apply lipschitzWith_of_nnNorm_deriv_le
      (fun t ↦ (hasDerivAt_smoothAbs hη t).differentiableAt)
    intro t
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_one, deriv_smoothAbs hη]
    exact Real.abs_div_sqrt_sq_add_le_one (sq_nonneg η) t

/-- The derivative of the approximation has absolute value at most one for every parameter. -/
theorem abs_deriv_smoothAbs_le_one (η t : ℝ) : |deriv (smoothAbs η) t| ≤ 1 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    (norm_deriv_le_of_lipschitz (x₀ := t) (lipschitzWith_smoothAbs η))

/-- The approximation is even in its argument. -/
@[simp]
theorem smoothAbs_neg (η t : ℝ) : smoothAbs η (-t) = smoothAbs η t := by
  simp [smoothAbs]

/-- Taking the absolute value of the argument does not change the approximation. -/
@[simp]
theorem smoothAbs_abs (η t : ℝ) : smoothAbs η |t| = smoothAbs η t := by
  simp [smoothAbs]

/-- The approximation is nonnegative for every parameter. -/
@[simp]
theorem smoothAbs_nonneg (η t : ℝ) : 0 ≤ smoothAbs η t :=
  sub_nonneg.2 (Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg t)))

/-- The absolute value of the approximation reduces to the approximation itself. -/
@[simp]
theorem abs_smoothAbs (η t : ℝ) : |smoothAbs η t| = smoothAbs η t :=
  abs_of_nonneg (smoothAbs_nonneg η t)

/-- For a nonnegative parameter, the approximation vanishes exactly at zero. -/
@[simp]
theorem smoothAbs_eq_zero_iff {η : ℝ} (hη : 0 ≤ η) (t : ℝ) :
    smoothAbs η t = 0 ↔ t = 0 := by
  rw [smoothAbs, sub_eq_zero]
  constructor
  · intro h
    have hs := Real.sq_sqrt (by positivity : 0 ≤ t ^ 2 + η ^ 2)
    rw [h] at hs
    nlinarith [sq_nonneg t]
  · rintro rfl
    simp [Real.sqrt_sq hη]

/-- For `η ≥ 0`, the approximation is bounded above by the absolute value. -/
theorem smoothAbs_le_abs {η : ℝ} (hη : 0 ≤ η) (t : ℝ) : smoothAbs η t ≤ |t| := by
  rw [smoothAbs, sub_le_iff_le_add]
  have h := Real.sqrt_add_le_add_sqrt (t ^ 2) (η ^ 2)
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hη] at h
  exact h

/-- For `η ≥ 0`, the approximation is within `η` of the absolute value, uniformly in `t`. -/
theorem abs_smoothAbs_sub_abs_le {η : ℝ} (hη : 0 ≤ η) (t : ℝ) : |smoothAbs η t - abs t| ≤ η := by
  rw [abs_le]
  exact ⟨by linarith [smoothAbs_def η t,
    Real.abs_le_sqrt (x := t) (le_add_of_nonneg_right (sq_nonneg η))],
    by linarith [smoothAbs_le_abs hη t]⟩

end TauCeti
