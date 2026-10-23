/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# The Laplace transform of `|sin|`

For `0 < a` the rectified sine `|sin t|` has the Laplace transform

`∫_{t > 0} |sin t| e^{-a t} dt = (1 + e^{-π a}) / ((1 - e^{-π a}) (1 + a²))`,

and, since `|sin|` is even, the two-sided transform
`∫_ℝ |sin t| e^{-a |t|} dt` is twice that. One arch contributes
`∫_0^π sin t e^{-a t} dt = (1 + e^{-π a}) / (1 + a²)`, and since `|sin|` is `π`-periodic every
later arch contributes the same amount damped by a further factor `e^{-π a}`; summing the
geometric series gives the closed form.

## Main declarations

* `TauCeti.integral_sin_mul_exp_neg_mul_zero_pi`: the integral over one arch;
* `TauCeti.integral_abs_sin_mul_exp_neg_mul_Ioi`: the one-sided Laplace transform of `|sin|`;
* `TauCeti.integral_abs_sin_mul_exp_neg_mul_abs`: the two-sided transform
  `∫_ℝ |sin t| e^{-a |t|} dt = 2 (1 + e^{-π a}) / ((1 - e^{-π a}) (1 + a²))`.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

/-- **The Laplace integral of `sin` over one arch.** For every real `a`,
`∫_0^π sin t e^{-a t} dt = (1 + e^{-π a}) / (1 + a²)`. -/
theorem integral_sin_mul_exp_neg_mul_zero_pi (a : ℝ) :
    ∫ t in (0 : ℝ)..π, Real.sin t * Real.exp (-(a * t)) =
      (1 + Real.exp (-(π * a))) / (1 + a ^ 2) := by
  -- `t ↦ -e^{-a t} (a sin t + cos t) / (1 + a²)` is an antiderivative.
  have ha : (1 + a ^ 2) ≠ 0 := by positivity
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t ↦ -(Real.exp (-(a * t)) * (a * Real.sin t + Real.cos t)) / (1 + a ^ 2))
      (Real.sin t * Real.exp (-(a * t))) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul a).neg.exp.mul
      (((Real.hasDerivAt_sin t).const_mul a).add (Real.hasDerivAt_cos t))).neg.div_const
        (1 + a ^ 2)
    refine h.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.add_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, Real.sin_pi,
    Real.cos_pi, mul_comm a π]
  field_simp
  ring

/-- For `0 < a`, the function `t ↦ |sin t| e^{-a t}` is integrable on `(0, ∞)`: it is
dominated by `e^{-a t}`. -/
theorem integrableOn_abs_sin_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t ↦ |Real.sin t| * Real.exp (-(a * t))) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-(a * t))) (Ioi 0) := by
    simpa using integrableOn_pow_mul_exp_neg_mul_Ioi 0 ha
  refine hexp.mono' (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, Real.abs_exp]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one t)

/-- **The Laplace transform of `|sin|`.** For `0 < a`,
`∫_{t > 0} |sin t| e^{-a t} dt = (1 + e^{-π a}) / ((1 - e^{-π a}) (1 + a²))`. -/
theorem integral_abs_sin_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), |Real.sin t| * Real.exp (-(a * t)) =
      (1 + Real.exp (-(π * a))) / ((1 - Real.exp (-(π * a))) * (1 + a ^ 2)) := by
  set f : ℝ → ℝ := fun t ↦ |Real.sin t| * Real.exp (-(a * t)) with hf
  set I := ∫ t in Ioi (0 : ℝ), f t with hI
  have hint := integrableOn_abs_sin_mul_exp_neg_mul_Ioi ha
  -- The first arch, where `|sin t| = sin t`.
  have harch : ∫ t in (0 : ℝ)..π, f t = (1 + Real.exp (-(π * a))) / (1 + a ^ 2) := by
    rw [← integral_sin_mul_exp_neg_mul_zero_pi a]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le Real.pi_pos.le] at ht
    simp only [hf, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)]
  -- The tail beyond the first arch is the whole integral damped by `e^{-π a}`.
  have htail : ∫ t in Ioi π, f t = Real.exp (-(π * a)) * I := by
    have hshift := (measurePreserving_add_right volume π).setIntegral_preimage_emb
      (measurableEmbedding_addRight π) f (Ioi π)
    rw [preimage_add_const_Ioi, sub_self] at hshift
    rw [← hshift, hI, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp only [hf, Real.sin_add_pi, abs_neg]
    rw [mul_left_comm, ← Real.exp_add]
    ring_nf
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi Real.pi_pos.le))
  rw [harch, htail] at hsplit
  rw [← hI] at hsplit
  have hlt : Real.exp (-(π * a)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hne : 1 - Real.exp (-(π * a)) ≠ 0 := (sub_pos.mpr hlt).ne'
  have key : (1 + Real.exp (-(π * a))) / (1 + a ^ 2) = I - Real.exp (-(π * a)) * I := by
    linarith
  rw [div_eq_iff (by positivity)] at key
  rw [eq_div_iff (mul_ne_zero hne (by positivity))]
  linear_combination -key

/-- For `0 < a`, the function `t ↦ |sin t| e^{-a |t|}` is integrable on `ℝ`: it is dominated by
`e^{-a |t|}`. -/
theorem integrable_abs_sin_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable fun t ↦ |Real.sin t| * Real.exp (-(a * |t|)) := by
  refine (integrable_exp_neg_mul_abs ha).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, Real.abs_exp]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one t)

/-- **The two-sided Laplace transform of `|sin|`.** For `0 < a`,
`∫_ℝ |sin t| e^{-a |t|} dt = 2 (1 + e^{-π a}) / ((1 - e^{-π a}) (1 + a²))`. -/
theorem integral_abs_sin_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    ∫ t, |Real.sin t| * Real.exp (-(a * |t|)) =
      2 * (1 + Real.exp (-(π * a))) / ((1 - Real.exp (-(π * a))) * (1 + a ^ 2)) := by
  have heven : (fun t ↦ |Real.sin t| * Real.exp (-(a * |t|))) =
      fun t ↦ |Real.sin (|t|)| * Real.exp (-(a * |t|)) := by
    ext t
    rcases abs_choice t with h | h <;> simp [h]
  rw [heven, integral_comp_abs (f := fun t ↦ |Real.sin t| * Real.exp (-(a * t))),
    integral_abs_sin_mul_exp_neg_mul_Ioi ha, mul_div_assoc]

end TauCeti
