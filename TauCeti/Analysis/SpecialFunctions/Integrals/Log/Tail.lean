/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmic bounds for weighted tail integrals

The tail with weight `t⁻²` of a summatory error bounded by `C t (log t)⁻ᵇ⁻¹` is bounded
by `(C / b) (log x)⁻ᵇ`. This is the logarithmic loss in passing from an unsmoothed prime
count to a normalized first Riesz remainder by partial summation.

The logarithmic substitution reduces the scalar majorant to the power tail from
`integral_Ioi_rpow_of_lt`. For the analytic number theory context, see Davenport,
*Multiplicative Number Theory*, third edition, Chapter 20 (prime number theorem for characters).
-/

public section

open Filter MeasureTheory Set

namespace TauCeti

open Real in
/-- For `b < -1`, the majorant `t⁻¹ (log t)^b` is integrable on `(x, ∞)` for any `x > 1`. -/
theorem integrableOn_Ioi_inv_mul_log_rpow {x b : ℝ} (hx : 1 < x) (hb : b < -1) :
    IntegrableOn (fun t : ℝ ↦ t⁻¹ * log t ^ b) (Ioi x) := by
  have h := integrableOn_comp_exp_Ioi (fun t : ℝ ↦ t⁻¹ * log t ^ b) (log x)
  rw [exp_log (zero_lt_one.trans hx)] at h
  exact h.mp (by simpa [smul_eq_mul, ← mul_assoc, (exp_pos _).ne'] using
    integrableOn_Ioi_rpow_of_lt hb (log_pos hx))

open Real in
/-- The exact integral of a logarithmic power against `dt/t` above `x > 1`. -/
theorem integral_Ioi_inv_mul_log_rpow {x b : ℝ} (hx : 1 < x) (hb : b < -1) :
    ∫ t in Ioi x, t⁻¹ * log t ^ b = -log x ^ (b + 1) / (b + 1) := by
  have h := integral_comp_exp_Ioi (fun t : ℝ ↦ t⁻¹ * log t ^ b) (log x)
  rw [exp_log (zero_lt_one.trans hx)] at h
  simpa [smul_eq_mul, ← mul_assoc, (exp_pos _).ne',
    integral_Ioi_rpow_of_lt hb (log_pos hx)] using h.symm

/-- The scalar majorant after applying the `t⁻²` weight to a summatory error. -/
private theorem norm_inv_sq_smul_le_log_majorant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E} {t b C : ℝ}
    (hv : ‖v‖ ≤ C * t * (Real.log t) ^ (-b - 1)) :
    ‖(t ^ 2)⁻¹ • v‖ ≤ C * (t⁻¹ * (Real.log t) ^ (-b - 1)) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (t ^ 2)⁻¹ * (C * t * (Real.log t) ^ (-b - 1)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by
      by_cases ht : t = 0
      · simp [ht]
      · field_simp

/-- A measurable summatory error with a logarithmic saving of exponent greater than one
is integrable against `dt/t²` above any cutoff where the bound holds. -/
theorem integrableOn_Ioi_inv_sq_smul_of_log_rpow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {x b C : ℝ}
    (hx : 1 < x) (hb : 0 < b) (hf : AEStronglyMeasurable f (volume.restrict (Ioi x)))
    (h : ∀ t ∈ Ioi x, ‖f t‖ ≤ C * t * (Real.log t) ^ (-b - 1)) :
    IntegrableOn (fun t ↦ (t ^ 2)⁻¹ • f t) (Ioi x) := by
  have hg := (integrableOn_Ioi_inv_mul_log_rpow hx (b := -b - 1) (by linarith)).const_mul C
  refine hg.mono' ((by fun_prop : Measurable (fun t : ℝ ↦ (t ^ 2)⁻¹)).aestronglyMeasurable.smul hf)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
  exact norm_inv_sq_smul_le_log_majorant (h t ht)

/-- A summatory error bounded on the tail by `C t (log t)^(-b-1)` contributes at most
`(C/b) (log x)^(-b)` to the tail integral with weight `t⁻²`. -/
theorem norm_integral_Ioi_inv_sq_smul_le_of_log_rpow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {x b C : ℝ}
    (hx : 1 < x) (hb : 0 < b)
    (h : ∀ t ∈ Ioi x, ‖f t‖ ≤ C * t * (Real.log t) ^ (-b - 1)) :
    ‖∫ t in Ioi x, (t ^ 2)⁻¹ • f t‖ ≤ (C / b) * (Real.log x) ^ (-b) := by
  have hb' : -b - 1 < -1 := by linarith
  calc
    _ ≤ ∫ t in Ioi x, C * (t⁻¹ * (Real.log t) ^ (-b - 1)) := by
      have hg := (integrableOn_Ioi_inv_mul_log_rpow hx hb').const_mul C
      exact norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Ioi
        fun t ht ↦ norm_inv_sq_smul_le_log_majorant (h t ht))
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_inv_mul_log_rpow hx hb', sub_add_cancel]
      ring

/-- A saving of `n + 2` logarithmic powers for the summatory error gives a saving of `n`
logarithmic powers for its weighted tail, with eventual constant one. -/
theorem eventually_norm_integral_Ioi_inv_sq_smul_le_inv_log_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {C : ℝ} {n : ℕ}
    (h : ∀ᶠ t in atTop, ‖f t‖ ≤ C * t / (Real.log t) ^ (n + 2)) :
    ∀ᶠ x in atTop, ‖∫ t in Ioi x, (t ^ 2)⁻¹ • f t‖ ≤ ((Real.log x) ^ n)⁻¹ := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  let b : ℝ := (n : ℝ) + 1
  have hb : 0 < b := by positivity
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (C / b)] with x hxT hx hlog
  refine (norm_integral_Ioi_inv_sq_smul_le_of_log_rpow hx hb (C := C) fun t ht ↦ ?_).trans ?_
  · have hexp : -b - 1 = -((n + 2 : ℕ) : ℝ) := by simp [b]; ring
    simpa only [hexp, Real.rpow_neg (Real.log_pos (hx.trans ht)).le, Real.rpow_natCast,
      div_eq_mul_inv] using hT t (hxT.trans (mem_Ioi.mp ht).le)
  · have hlog₀ := Real.log_pos hx
    have hexp : -b = -((n + 1 : ℕ) : ℝ) := by simp [b]
    rw [hexp, Real.rpow_neg hlog₀.le, Real.rpow_natCast, pow_succ, mul_inv_rev, ← mul_assoc]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hlog₀).mpr hlog)

end TauCeti
