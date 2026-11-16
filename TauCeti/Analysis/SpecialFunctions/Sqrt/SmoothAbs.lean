/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A smooth approximation of the absolute value

For a real parameter `η`, the function `TauCeti.smoothAbs η : t ↦ √(t ^ 2 + η ^ 2) - η` is the
absolute value for `η = 0` and is smooth for `η ≠ 0`, with derivative `t / √(t ^ 2 + η ^ 2)` of
absolute value at most `1`. For `η ≥ 0` it vanishes at `0`, lies between `0` and `|t|`, and is
within `η` of `|t|`.

Composing a function `u` with `smoothAbs η` therefore gives smooth functions converging uniformly
to `|u|` as `η → 0`, with pointwise gradients `|∇(smoothAbs η ∘ u)| ≤ |∇u|`. This is how `|u|` is
shown to lie in a Sobolev space defined as a completion of smooth functions, with no larger energy
than `u`.

## Main declarations

* `TauCeti.smoothAbs`: the function `t ↦ √(t ^ 2 + η ^ 2) - η`.
* `TauCeti.contDiff_smoothAbs`, `TauCeti.hasDerivAt_smoothAbs`: its smoothness and derivative for
  `η ≠ 0`.
* `TauCeti.abs_div_sqrt_sq_add_sq_le_one`: the derivative has absolute value at most `1`.
* `TauCeti.abs_smoothAbs_sub_abs_le`: `smoothAbs η` is within `η` of the absolute value.
-/

public section

noncomputable section

namespace TauCeti

/-- The function `t ↦ √(t ^ 2 + η ^ 2) - η`, a smooth approximation of `|t|` for small `η ≠ 0`. -/
def smoothAbs (η t : ℝ) : ℝ := √(t ^ 2 + η ^ 2) - η

theorem smoothAbs_def (η t : ℝ) : smoothAbs η t = √(t ^ 2 + η ^ 2) - η := by
  rw [smoothAbs]

@[simp]
theorem smoothAbs_zero_left (t : ℝ) : smoothAbs 0 t = |t| := by
  simp [smoothAbs, Real.sqrt_sq_eq_abs]

theorem smoothAbs_zero_right {η : ℝ} (hη : 0 ≤ η) : smoothAbs η 0 = 0 := by
  simp [smoothAbs, Real.sqrt_sq hη]

theorem contDiff_smoothAbs {η : ℝ} (hη : η ≠ 0) {n : WithTop ℕ∞} : ContDiff ℝ n (smoothAbs η) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t ↦ by positivity) |>.sub contDiff_const

theorem hasDerivAt_smoothAbs {η : ℝ} (hη : η ≠ 0) (t : ℝ) :
    HasDerivAt (smoothAbs η) (t / √(t ^ 2 + η ^ 2)) t := by
  have h := (((hasDerivAt_pow 2 t).add_const (η ^ 2)).sqrt (by positivity)).sub_const η
  convert h using 1
  · ext x
    rw [smoothAbs]
  rw [Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, mul_div_mul_left _ _ two_ne_zero]

/-- The derivative `t / √(t ^ 2 + η ^ 2)` of `smoothAbs η` has absolute value at most `1`. -/
theorem abs_div_sqrt_sq_add_sq_le_one (t η : ℝ) : |t / √(t ^ 2 + η ^ 2)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem abs_smoothAbs_sub_abs_le {η : ℝ} (hη : 0 ≤ η) (t : ℝ) : |smoothAbs η t - abs t| ≤ η := by
  have h1 : |t| ≤ √(t ^ 2 + η ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(t ^ 2 + η ^ 2) ≤ |t| + η := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t]
  rw [smoothAbs, abs_le]
  constructor <;> linarith

theorem smoothAbs_nonneg (η t : ℝ) : 0 ≤ smoothAbs η t := by
  rw [smoothAbs, sub_nonneg]
  calc η ≤ |η| := le_abs_self η
    _ = √(η ^ 2) := (Real.sqrt_sq_eq_abs η).symm
    _ ≤ √(t ^ 2 + η ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

theorem smoothAbs_le_abs {η : ℝ} (hη : 0 ≤ η) (t : ℝ) : smoothAbs η t ≤ |t| := by
  rw [smoothAbs, sub_le_iff_le_add, Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg t, sq_abs t]

theorem abs_smoothAbs_le {η : ℝ} (hη : 0 ≤ η) (t : ℝ) : |smoothAbs η t| ≤ |t| := by
  rw [abs_of_nonneg (smoothAbs_nonneg η t)]
  exact smoothAbs_le_abs hη t

end TauCeti
