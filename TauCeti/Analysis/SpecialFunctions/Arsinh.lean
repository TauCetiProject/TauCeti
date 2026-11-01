/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The inverse of the normalized hyperbolic sine

Mathlib's `Analysis/SpecialFunctions/Arsinh.lean` introduces `Real.arsinh`, the inverse of
`Real.sinh`, and proves that it is strictly monotone and smooth, with derivative
`1 / √(1 + x²)`. This file studies the inverse `β` of the *normalized* hyperbolic sine
`t ↦ sinh t / sinh 1 = (eᵗ - e⁻ᵗ) / (e - e⁻¹)`, which is the rescaling of `Real.arsinh` that
fixes `0` and `± 1`.

## Main declarations

* `TauCeti.normalizedArsinh`: the function `β s = arsinh (sinh 1 * s)`, inverse to
  `t ↦ sinh t / sinh 1` (`TauCeti.sinh_normalizedArsinh_div`, `TauCeti.normalizedArsinh_sinh_div`).
* `TauCeti.normalizedArsinh_strictMono`, `TauCeti.abs_normalizedArsinh_lt_one_iff`: `β` is
  increasing, odd, fixes `0` and `± 1`, and so maps `(-1, 1)` onto itself.
* `TauCeti.analyticAt_normalizedArsinh`: `β` is analytic at every point.
* `TauCeti.deriv_normalizedArsinh_pos`, `TauCeti.deriv_normalizedArsinh_le_two`,
  `TauCeti.abs_mul_deriv_normalizedArsinh_le_one`: the derivative satisfies `0 < β' s ≤ 2` and
  `|s| * β' s ≤ 1`, that is, `|β' s| ≤ min 2 (1 / |s|)` for `s ≠ 0`.

Where it is used: `TauCeti/Analysis/Analytic/HeightCompression.lean` compresses the height of
a cylinder `E × ℝ` by `β`, following S. Łojasiewicz, *Triangulation of semi-analytic sets*,
Annali della Scuola Normale Superiore di Pisa (3) 18 (1964), 449–474, §2, Lemma 10.
-/

public section

open Real

namespace TauCeti

/-- The inverse `β` of the normalized hyperbolic sine `t ↦ sinh t / sinh 1`, that is, of
`t ↦ (eᵗ - e⁻ᵗ) / (e - e⁻¹)`: `β s = arsinh (sinh 1 * s)`. It is an increasing analytic
bijection of `ℝ` fixing `0` and `± 1`. -/
noncomputable def normalizedArsinh (s : ℝ) : ℝ :=
  arsinh (sinh 1 * s)

theorem normalizedArsinh_apply (s : ℝ) : normalizedArsinh s = arsinh (sinh 1 * s) :=
  (rfl)

@[simp]
theorem sinh_normalizedArsinh_div (s : ℝ) : sinh (normalizedArsinh s) / sinh 1 = s := by
  rw [normalizedArsinh_apply, sinh_arsinh, mul_div_cancel_left₀ _ (sinh_pos_iff.2 one_pos).ne']

@[simp]
theorem normalizedArsinh_sinh_div (t : ℝ) : normalizedArsinh (sinh t / sinh 1) = t := by
  rw [normalizedArsinh_apply, mul_div_cancel₀ _ (sinh_pos_iff.2 one_pos).ne', arsinh_sinh]

/-- `β` is strictly increasing. -/
theorem normalizedArsinh_strictMono : StrictMono normalizedArsinh := by
  rw [funext normalizedArsinh_apply]
  exact arsinh_strictMono.comp (strictMono_mul_left_of_pos (sinh_pos_iff.2 one_pos))

@[simp]
theorem normalizedArsinh_lt_normalizedArsinh {s s' : ℝ} :
    normalizedArsinh s < normalizedArsinh s' ↔ s < s' :=
  normalizedArsinh_strictMono.lt_iff_lt

@[simp]
theorem normalizedArsinh_le_normalizedArsinh {s s' : ℝ} :
    normalizedArsinh s ≤ normalizedArsinh s' ↔ s ≤ s' :=
  normalizedArsinh_strictMono.le_iff_le

@[simp]
theorem normalizedArsinh_zero : normalizedArsinh 0 = 0 := by
  simp [normalizedArsinh_apply]

@[simp]
theorem normalizedArsinh_one : normalizedArsinh 1 = 1 := by
  simp [normalizedArsinh_apply]

@[simp]
theorem normalizedArsinh_neg (s : ℝ) : normalizedArsinh (-s) = -normalizedArsinh s := by
  simp [normalizedArsinh_apply]

/-- `β` maps the open interval `(-1, 1)` onto itself, and its complement onto its complement. -/
@[simp]
theorem abs_normalizedArsinh_lt_one_iff {s : ℝ} : |normalizedArsinh s| < 1 ↔ |s| < 1 := by
  conv_lhs => rw [← normalizedArsinh_one]
  rw [abs_lt, abs_lt, ← normalizedArsinh_neg, normalizedArsinh_lt_normalizedArsinh,
    normalizedArsinh_lt_normalizedArsinh]

/-- `β` is smooth, indeed `C^n` for every `n`, including `n = ω`. -/
@[fun_prop]
theorem contDiff_normalizedArsinh {n : WithTop ℕ∞} : ContDiff ℝ n normalizedArsinh := by
  rw [funext normalizedArsinh_apply]
  fun_prop

/-- `β` is analytic at every point. -/
@[fun_prop]
theorem analyticAt_normalizedArsinh (s : ℝ) : AnalyticAt ℝ normalizedArsinh s :=
  contDiff_normalizedArsinh.contDiffAt.analyticAt

/-- The derivative of `β` at `s` is `sinh 1 / √(1 + (sinh 1 * s)²)`. -/
theorem hasDerivAt_normalizedArsinh (s : ℝ) :
    HasDerivAt normalizedArsinh (sinh 1 / √(1 + (sinh 1 * s) ^ 2)) s := by
  rw [funext normalizedArsinh_apply]
  simpa [div_eq_inv_mul] using ((hasDerivAt_id s).const_mul (sinh 1)).arsinh

/-- The derivative of `β` at `s` is `sinh 1 / √(1 + (sinh 1 * s)²)`. -/
theorem deriv_normalizedArsinh (s : ℝ) :
    deriv normalizedArsinh s = sinh 1 / √(1 + (sinh 1 * s) ^ 2) :=
  (hasDerivAt_normalizedArsinh s).deriv

/-- The derivative of `β` is everywhere positive. -/
theorem deriv_normalizedArsinh_pos (s : ℝ) : 0 < deriv normalizedArsinh s := by
  rw [deriv_normalizedArsinh]
  exact div_pos (sinh_pos_iff.2 one_pos) (sqrt_pos.2 (by positivity))

/-- The derivative of `β` is at most `2`. -/
theorem deriv_normalizedArsinh_le_two (s : ℝ) : deriv normalizedArsinh s ≤ 2 := by
  have hsinh : sinh 1 < 2 := by
    rw [sinh_eq]
    linarith [exp_pos (-1), exp_one_lt_d9]
  rw [deriv_normalizedArsinh]
  refine (div_le_self (sinh_pos_iff.2 one_pos).le ?_).trans hsinh.le
  exact one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))

/-- For `s ≠ 0`, the derivative of `β` at `s` is at most `1 / |s|`. It is stated in the form
`|s| * β' s ≤ 1`, which also holds at `s = 0`. -/
theorem abs_mul_deriv_normalizedArsinh_le_one (s : ℝ) : |s| * deriv normalizedArsinh s ≤ 1 := by
  have h1 : 0 < sinh 1 := sinh_pos_iff.2 one_pos
  calc |s| * deriv normalizedArsinh s = |sinh 1 * s| / √(1 + (sinh 1 * s) ^ 2) := by
        rw [deriv_normalizedArsinh, abs_mul, abs_of_pos h1]; ring
    _ ≤ 1 := div_le_one_of_le₀ (abs_le_sqrt (le_add_of_nonneg_left zero_le_one)) (sqrt_nonneg _)

end TauCeti
