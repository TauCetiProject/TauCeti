/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.SpecialFunctions.Exp.Image

/-!
# Logarithmic moment integrals on the unit interval

For real exponents `r > -1` and `q > -1`, the substitution `t = exp (-u)` carries the unit-interval
integral `∫₀¹ t ^ r * (-log t) ^ q dt` onto the Gamma integral
`∫_{u > 0} u ^ q * exp (-(r + 1) * u) du = Γ(q + 1) / (r + 1) ^ (q + 1)`.
When `q = k` is a natural number, `Γ(k + 1) = k!` yields the real-exponent evaluation
`∫₀¹ t ^ r * (-log t) ^ k dt = k! / (r + 1) ^ (k + 1)` and its natural-moment specialization
`∫₀¹ t ^ j * (-log t) ^ k dt = k! / (j + 1) ^ (k + 1)`.

The first moment `t ↦ t * log t` also has an elementary antiderivative, which evaluates its
integral over every interval, including the planar radial integrals `∫ ρ log ρ dρ`.

## Main results

* `TauCeti.integrableOn_Ioo_rpow_mul_neg_log_rpow` and
  `TauCeti.intervalIntegrable_rpow_mul_neg_log_rpow`: integrability on `(0, 1)` and `[0, 1]` for
  `r > -1` and `q > -1`.
* `TauCeti.integral_rpow_mul_neg_log_rpow`:
  `∫ t in 0..1, t ^ r * (-log t) ^ q = Γ(q + 1) / (r + 1) ^ (q + 1)`.
* `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`, `TauCeti.integral_rpow_mul_neg_log_pow`,
  `TauCeti.intervalIntegrable_rpow_mul_log_pow`, and `TauCeti.integral_rpow_mul_log_pow`:
  interval integrability on any interval `a..b` and unit-interval evaluation for the natural
  logarithmic power cases `(-log t) ^ k` and `(log t) ^ k`.
* `TauCeti.intervalIntegrable_pow_mul_neg_log_pow`, `TauCeti.integral_pow_mul_neg_log_pow`,
  `TauCeti.intervalIntegrable_pow_mul_log_pow`, and `TauCeti.integral_pow_mul_log_pow`:
  interval integrability on any interval `a..b` and unit-interval evaluation for the natural
  polynomial-moment specializations `t ^ j * (-log t) ^ k` and `t ^ j * (log t) ^ k`.
* `TauCeti.integral_mul_log`:
  `∫ t in a..b, t * log t = (b ^ 2 * log b - a ^ 2 * log a) / 2 - (b ^ 2 - a ^ 2) / 4` for all
  `a` and `b`.
-/

public section

namespace TauCeti

open MeasureTheory Real Set

private theorem exp_neg_pullback {r q u : ℝ} :
    |exp (-u) * -1| • ((exp (-u)) ^ r * (-log (exp (-u))) ^ q) =
      u ^ q * exp (-(r + 1) * u) := by
  simp only [mul_neg_one, abs_neg, abs_exp, smul_eq_mul, ← exp_mul, log_exp, neg_neg]
  rw [← mul_assoc, ← exp_add, mul_comm]
  congr 2
  ring

/-- For `r > -1` and `q > -1`, the logarithmic weight `t ^ r * (-log t) ^ q` is integrable on
`(0, 1)`. -/
theorem integrableOn_Ioo_rpow_mul_neg_log_rpow {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    IntegrableOn (fun t : ℝ ↦ t ^ r * (-log t) ^ q) (Ioo 0 1) := by
  have hb : 0 < r + 1 := by linarith
  suffices IntegrableOn (fun t : ℝ ↦ t ^ r * (-log t) ^ q) ((fun u : ℝ ↦ exp (-u)) '' Ioi 0) by
    simpa using this
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _ ↦ ((hasDerivAt_neg u).exp).hasDerivWithinAt) (exp_injective.comp neg_injective).injOn]
  exact (integrableOn_rpow_mul_exp_neg_mul_rpow hq zero_lt_one hb).congr_fun
    (fun u _ ↦ by simp only [exp_neg_pullback, rpow_one]) measurableSet_Ioi

/-- For `r > -1` and `q > -1`, `t ↦ t ^ r * (-log t) ^ q` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_mul_neg_log_rpow {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ q) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact integrableOn_Ioo_rpow_mul_neg_log_rpow hr hq

/-- For `r > -1` and `q > -1`, the logarithmic moment integral over `[0, 1]` evaluates to
`Γ(q + 1) / (r + 1) ^ (q + 1)`. -/
theorem integral_rpow_mul_neg_log_rpow {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ q = Gamma (q + 1) / (r + 1) ^ (q + 1) := by
  have hb : 0 < r + 1 := by linarith
  have hIoo : ∫ t in Ioo (0 : ℝ) 1, t ^ r * (-log t) ^ q =
      ∫ t in (fun u : ℝ ↦ exp (-u)) '' Ioi 0, t ^ r * (-log t) ^ q := by simp
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hIoo,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ ↦ ((hasDerivAt_neg u).exp).hasDerivWithinAt)
      (exp_injective.comp neg_injective).injOn]
  have hcongr :
      ∫ u in Ioi (0 : ℝ), |exp (-u) * -1| • ((exp (-u)) ^ r * (-log (exp (-u))) ^ q) =
        ∫ u in Ioi (0 : ℝ), u ^ q * exp (-(r + 1) * u ^ (1 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ by rw [exp_neg_pullback, rpow_one]
  rw [hcongr, integral_rpow_mul_exp_neg_mul_rpow zero_lt_one hq hb]
  simp [-neg_add_rev, rpow_neg hb.le, inv_mul_eq_div]

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (-log t) ^ k` is interval integrable on every
interval. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ k) volume a b := by
  have h01 : IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ k) volume 0 1 := by
    have hk : (-1 : ℝ) < k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    simpa only [rpow_natCast] using intervalIntegrable_rpow_mul_neg_log_rpow hr hk
  have hnonneg (c : ℝ) (hc : 0 ≤ c) :
      IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ k) volume 0 c := by
    rcases le_or_gt c 1 with hc1 | hc1
    · exact h01.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc.mpr (Or.inl ⟨hc, hc1⟩)))
    · have h1c : ContinuousOn (fun t : ℝ ↦ t ^ r * (-log t) ^ k) (uIcc 1 c) := by
        rw [uIcc_of_le hc1.le]
        refine ContinuousOn.mul
          (continuousOn_id.rpow_const fun _ ht ↦ Or.inl (zero_lt_one.trans_le ht.1).ne')
          ((continuousOn_log.mono fun t (ht : t ∈ Icc 1 c) ↦
            (zero_lt_one.trans_le ht.1).ne').neg.pow k)
      exact h01.trans h1c.intervalIntegrable
  have hall (c : ℝ) : IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ k) volume 0 c := by
    rcases le_total 0 c with hc | hc
    · exact hnonneg c hc
    · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
      have m := (hnonneg (-c) (by linarith)).const_mul (cos (r * π))
      rw [intervalIntegrable_iff] at m ⊢
      refine m.congr_fun (fun t ht ↦ ?_) measurableSet_uIoc
      rw [uIoc_of_le (by linarith : 0 ≤ -c)] at ht
      simp only [log_neg_eq_log, rpow_def_of_pos ht.1,
        rpow_def_of_neg (by linarith [ht.1] : -t < 0)]
      ring
  exact (hall a).symm.trans (hall b)

/-- For `r > -1` and `k : ℕ`, `∫₀¹ t ^ r * (-log t) ^ k dt = k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ k = (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hk : (-1 : ℝ) < k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := integral_rpow_mul_neg_log_rpow hr hk
  rw [Gamma_nat_eq_factorial] at h
  simpa only [rpow_natCast, ← Nat.cast_add_one] using h

private lemma rpow_mul_log_pow_eq (r : ℝ) (k : ℕ) :
    (fun t : ℝ ↦ t ^ r * log t ^ k) = fun t : ℝ ↦ (-1) ^ k * (t ^ r * (-log t) ^ k) := by
  ext t
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by simp [← mul_pow]
  rw [neg_pow]
  linear_combination -t ^ r * log t ^ k * hsign

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (log t) ^ k` is interval integrable on every
interval. -/
theorem intervalIntegrable_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * log t ^ k) volume a b := by
  rw [rpow_mul_log_pow_eq]
  exact (intervalIntegrable_rpow_mul_neg_log_pow hr k).const_mul ((-1) ^ k)

/-- For `r > -1` and `k : ℕ`, `∫₀¹ t ^ r * (log t) ^ k dt = (-1) ^ k * k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ r * log t ^ k = (-1) ^ k * (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  rw [rpow_mul_log_pow_eq, intervalIntegral.integral_const_mul,
    integral_rpow_mul_neg_log_pow hr k, mul_div_assoc]

/-- For natural numbers `j` and `k`, `t ↦ t ^ j * (-log t) ^ k` is interval integrable on every
interval. -/
theorem intervalIntegrable_pow_mul_neg_log_pow (j k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ j * (-log t) ^ k) volume a b := by
  simpa only [rpow_natCast] using
    intervalIntegrable_rpow_mul_neg_log_pow (r := j) (by linarith [Nat.cast_nonneg (α := ℝ) j]) k

/-- For natural numbers `j` and `k`, `∫₀¹ t ^ j * (-log t) ^ k dt = k! / (j + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (j k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ j * (-log t) ^ k = (k.factorial : ℝ) / (j + 1 : ℝ) ^ (k + 1) := by
  simpa only [rpow_natCast] using
    integral_rpow_mul_neg_log_pow (r := j) (by linarith [Nat.cast_nonneg (α := ℝ) j]) k

/-- For natural numbers `j` and `k`, `t ↦ t ^ j * (log t) ^ k` is interval integrable on every
interval. -/
theorem intervalIntegrable_pow_mul_log_pow (j k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ j * log t ^ k) volume a b := by
  simpa only [rpow_natCast] using
    intervalIntegrable_rpow_mul_log_pow (r := j) (by linarith [Nat.cast_nonneg (α := ℝ) j]) k

/-- For natural numbers `j` and `k`,
`∫₀¹ t ^ j * (log t) ^ k dt = (-1) ^ k * k! / (j + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_log_pow (j k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ j * log t ^ k =
      (-1) ^ k * (k.factorial : ℝ) / (j + 1 : ℝ) ^ (k + 1) := by
  simpa only [rpow_natCast] using
    integral_rpow_mul_log_pow (r := j) (by linarith [Nat.cast_nonneg (α := ℝ) j]) k

/-- The integral of `t ↦ t * log t` over any interval, with antiderivative
`t ↦ t ^ 2 * log t / 2 - t ^ 2 / 4`. Lean's convention `log t = log |t|` makes the formula hold
on intervals containing or crossing `0`. -/
@[simp]
theorem integral_mul_log (a b : ℝ) :
    ∫ t in a..b, t * log t = (b ^ 2 * log b - a ^ 2 * log a) / 2 - (b ^ 2 - a ^ 2) / 4 := by
  have hF : Continuous fun t : ℝ ↦ t * (t * log t) / 2 - t ^ 2 / 4 :=
    ((continuous_id.mul continuous_mul_log).div_const 2).sub (by fun_prop)
  -- The derivative is computed through `log`, so off the negligible point `0`.
  rw [integral_eq_of_hasDerivAt_off_countable _ _ (countable_singleton 0) hF.continuousOn
    (fun t ht ↦ ?_) (continuous_mul_log.intervalIntegrable a b)]
  · ring
  · convert (((hasDerivAt_id' t).mul (hasDerivAt_mul_log ht.2)).div_const 2).sub
      ((hasDerivAt_pow 2 t).div_const 4) using 1
    ring

end TauCeti
