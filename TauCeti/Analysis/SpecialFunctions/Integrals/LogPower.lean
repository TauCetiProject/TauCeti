/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic moment integrals on the unit interval

Under the substitution `t = exp (-u)`, the open unit interval `(0, 1)` corresponds to the positive
half-line `(0, ∞)` with Jacobian `exp (-u)`. Applying this change of variables turns the
logarithmic moment integral `∫ t in 0..1, t ^ r * (-log t) ^ q` into Euler's Gamma integral at
`q + 1` scaled by `r + 1`, giving `Γ(q + 1) / (r + 1) ^ (q + 1)` whenever `r > -1` and `q > -1`.

For natural logarithmic exponents `k : ℕ`, `Γ(k + 1) = k!` yields the rational moments
`k! / (r + 1) ^ (k + 1)` and, for signed powers `(log t) ^ k`, `(-1) ^ k * k! / (r + 1) ^ (k + 1)`.
These moments evaluate termwise radial integrals of power series against `(-log t) ^ k`.

## Main declarations

* `TauCeti.integrableOn_Ioo_zero_one_iff_comp_exp_neg`,
  `TauCeti.integral_Ioo_zero_one_eq_integral_comp_exp_neg`: the substitution `t = exp (-u)`
  between `(0, 1)` and `(0, ∞)` for Banach-space-valued integrands.
* `TauCeti.intervalIntegrable_rpow_mul_neg_log_rpow`,
  `TauCeti.integral_rpow_mul_neg_log_rpow`: `∫ t in 0..1, t ^ r * (-log t) ^ q =
  Γ(q + 1) / (r + 1) ^ (q + 1)` for `r > -1` and `q > -1`.
* `TauCeti.integral_rpow_mul_neg_log_pow`, `TauCeti.integral_pow_mul_neg_log_pow`,
  `TauCeti.integral_neg_log_pow`: natural-power specializations in terms of factorials.
* `TauCeti.integral_rpow_mul_log_pow`, `TauCeti.integral_log_pow`: signed `(log t) ^ k` variants.
-/

public section

open MeasureTheory Real Set

namespace TauCeti

/-- The map `u ↦ exp (-u)` carries `(0, ∞)` onto `(0, 1)`. -/
theorem image_exp_neg_Ioi : (fun u : ℝ ↦ exp (-u)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext t
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨exp_pos (-u), exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)⟩
  · rintro ⟨ht0, ht1⟩
    exact ⟨-log t, neg_pos.mpr (log_neg ht0 ht1), by rw [neg_neg, exp_log ht0]⟩

/-- Integrability on `(0, 1)` is equivalent to integrability on `(0, ∞)` under `t = exp (-u)`. -/
theorem integrableOn_Ioo_zero_one_iff_comp_exp_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    IntegrableOn g (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun u : ℝ ↦ exp (-u) • g (exp (-u))) (Ioi (0 : ℝ)) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ ↦ exp (-x)) (-exp (-u)) (Ioi 0) u :=
    fun u _ ↦ ((hasDerivAt_neg u).exp.congr_deriv (by ring)).hasDerivWithinAt
  rw [← image_exp_neg_Ioi, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hderiv (fun u _ v _ huv ↦ neg_injective (exp_injective huv)) g]
  refine integrableOn_congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  simp [abs_of_pos (exp_pos (-u))]

/-- Substitution `t = exp (-u)` turns an integral over `(0, 1)` into an integral over `(0, ∞)`. -/
theorem integral_Ioo_zero_one_eq_integral_comp_exp_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ t in Ioo (0 : ℝ) 1, g t = ∫ u in Ioi (0 : ℝ), exp (-u) • g (exp (-u)) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ ↦ exp (-x)) (-exp (-u)) (Ioi 0) u :=
    fun u _ ↦ ((hasDerivAt_neg u).exp.congr_deriv (by ring)).hasDerivWithinAt
  rw [← image_exp_neg_Ioi, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hderiv (fun u _ v _ huv ↦ neg_injective (exp_injective huv)) g]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  simp [abs_of_pos (exp_pos (-u))]

private lemma exp_neg_smul_rpow_mul_neg_log_rpow (r q u : ℝ) :
    exp (-u) • ((exp (-u)) ^ r * (-log (exp (-u))) ^ q) =
      u ^ q * exp (-(r + 1) * u ^ (1 : ℝ)) := by
  have hexp : -u + -u * r = -(r + 1) * u := by ring
  simp only [smul_eq_mul, log_exp, neg_neg, rpow_one]
  rw [← exp_mul, ← mul_assoc, ← exp_add, hexp, mul_comm]

/-- For `r > -1` and `q > -1`, `t ↦ t ^ r * (-log t) ^ q` is integrable on `(0, 1)`. -/
theorem integrableOn_rpow_mul_neg_log_rpow_Ioo {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    IntegrableOn (fun t : ℝ ↦ t ^ r * (-log t) ^ q) (Ioo (0 : ℝ) 1) := by
  rw [integrableOn_Ioo_zero_one_iff_comp_exp_neg]
  exact (integrableOn_rpow_mul_exp_neg_mul_rpow hq zero_lt_one
    (by linarith : 0 < r + 1)).congr_fun
    (fun u _ ↦ (exp_neg_smul_rpow_mul_neg_log_rpow r q u).symm) measurableSet_Ioi

/-- For `r > -1` and `q > -1`, `t ↦ t ^ r * (-log t) ^ q` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_mul_neg_log_rpow {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ q) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    (integrableOn_rpow_mul_neg_log_rpow_Ioo hr hq)

/-- For `r > -1` and `q > -1`,
`∫ t in 0..1, t ^ r * (-log t) ^ q = Γ(q + 1) / (r + 1) ^ (q + 1)`. -/
theorem integral_rpow_mul_neg_log_rpow {r q : ℝ} (hr : -1 < r) (hq : -1 < q) :
    ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ q = Gamma (q + 1) / (r + 1) ^ (q + 1) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_Ioo_zero_one_eq_integral_comp_exp_neg]
  have hcongr : ∫ u in Ioi (0 : ℝ), exp (-u) • ((exp (-u)) ^ r * (-log (exp (-u))) ^ q) =
      ∫ u in Ioi (0 : ℝ), u ^ q * exp (-(r + 1) * u ^ (1 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ exp_neg_smul_rpow_mul_neg_log_rpow r q u
  rw [hcongr, integral_rpow_mul_exp_neg_mul_rpow zero_lt_one hq hr1]
  simp only [div_one, mul_one]
  rw [rpow_neg hr1.le, inv_mul_eq_div]

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (-log t) ^ k` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-log t) ^ k) volume 0 1 := by
  have hk : (-1 : ℝ) < k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  refine (intervalIntegrable_rpow_mul_neg_log_rpow hr hk).congr_ae ?_
  rw [uIoc_of_le zero_le_one]
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun t _ ↦ by simp [rpow_natCast]

/-- For `r > -1` and `k : ℕ`, `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ k = (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hk : (-1 : ℝ) < k := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hcongr : ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ k =
      ∫ t in (0 : ℝ)..1, t ^ r * (-log t) ^ (k : ℝ) :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ ↦ by simp [rpow_natCast])
  rw [hcongr, integral_rpow_mul_neg_log_rpow hr hk, Gamma_nat_eq_factorial,
    ← Nat.cast_add_one, rpow_natCast]

/-- For `r > -1` and `k : ℕ`,
`∫ t in 0..1, t ^ r * (log t) ^ k = (-1) ^ k * k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ r * log t ^ k =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hcongr : (fun t : ℝ ↦ t ^ r * log t ^ k) =
      fun t : ℝ ↦ (-1 : ℝ) ^ k * (t ^ r * (-log t) ^ k) := by
    ext t
    have hlog : log t = (-1 : ℝ) * (-log t) := by ring
    conv_lhs => rw [hlog, mul_pow]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_rpow_mul_neg_log_pow hr k,
    mul_div_assoc]

/-- For `m k : ℕ`, `t ↦ t ^ m * (-log t) ^ k` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_pow_mul_neg_log_pow (m k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * (-log t) ^ k) volume 0 1 := by
  have hm : (-1 : ℝ) < m := by linarith [Nat.cast_nonneg (α := ℝ) m]
  simpa [rpow_natCast] using intervalIntegrable_rpow_mul_neg_log_pow hm k

/-- For `m k : ℕ`, `∫ t in 0..1, t ^ m * (-log t) ^ k = k! / (m + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (m k : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ m * (-log t) ^ k = (k.factorial : ℝ) / (m + 1 : ℝ) ^ (k + 1) := by
  have hm : (-1 : ℝ) < m := by linarith [Nat.cast_nonneg (α := ℝ) m]
  simpa [rpow_natCast] using integral_rpow_mul_neg_log_pow hm k

/-- For `k : ℕ`, `∫ t in 0..1, (-log t) ^ k = k!`. -/
theorem integral_neg_log_pow (k : ℕ) :
    ∫ t in (0 : ℝ)..1, (-log t) ^ k = k.factorial := by
  simpa using integral_pow_mul_neg_log_pow 0 k

/-- For `k : ℕ`, `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`. -/
theorem integral_log_pow (k : ℕ) :
    ∫ t in (0 : ℝ)..1, log t ^ k = (-1 : ℝ) ^ k * k.factorial := by
  simpa using integral_rpow_mul_log_pow (r := 0) neg_one_lt_zero k

end TauCeti
