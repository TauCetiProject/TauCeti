/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.SpecialFunctions.Exp.Image
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Logarithmic moment integrals on the unit interval

For real exponents `r > -1` and `q > -1`, the substitution `t = exp (-u)` carries the unit-interval
integral `∫₀¹ t ^ r * (-log t) ^ q dt` onto the Gamma integral
`∫_{u > 0} u ^ q * exp (-(r + 1) * u) du = Γ(q + 1) / (r + 1) ^ (q + 1)`.
When `q = k` is a natural number, `Γ(k + 1) = k!` yields the real-exponent evaluation
`∫₀¹ t ^ r * (-log t) ^ k dt = k! / (r + 1) ^ (k + 1)` and its natural-moment specialization
`∫₀¹ t ^ j * (-log t) ^ k dt = k! / (j + 1) ^ (k + 1)`.

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
* `Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi`:
  integrability of `t ↦ |log t| ^ k * t ^ s * exp (-b * t)` on `(0, ∞)` for `s > -1` and `b > 0`.
* `Complex.integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi`,
  `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`: complex integrability of
  `t ↦ t^s (log t)^k e^{-wt}` on `(0, ∞)` for `Re s > -1`, `Re w > 0` and its `k = 0` case.
* `IsCompact.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le`: uniform integrable
  real majorant on compact subsets of `{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}`.
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

end TauCeti

/-- For `s > -1`, `b > 0`, and any natural power `k`, `t ↦ |log t|^k t^s e^{-bt}` is integrable
on `(0, ∞)`. -/
theorem Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi {s b : ℝ} (hs : -1 < s)
    (hb : 0 < b) (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Set.Ioi 0) := by
  open MeasureTheory Set in
  have hm : AEStronglyMeasurable (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t))
      volume := (Measurable.aestronglyMeasurable (by fun_prop))
  have hIoo :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioo 0 1) := by
    refine (TauCeti.integrableOn_Ioo_rpow_mul_neg_log_rpow hs
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1 : ℝ) < k)).mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have hlog : Real.log t < 0 := Real.log_neg ht.1 ht.2
    have hlog_nn : 0 ≤ -Real.log t := neg_nonneg.mpr hlog.le
    have hexp : Real.exp (-b * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_of_nonneg (by positivity), abs_of_neg hlog, ← Real.rpow_natCast (-Real.log t) k]
    calc (-Real.log t) ^ (k : ℝ) * t ^ s * Real.exp (-b * t)
        ≤ (-Real.log t) ^ (k : ℝ) * t ^ s * 1 := by gcongr
      _ = t ^ s * (-Real.log t) ^ (k : ℝ) := by ring
  have hIoc :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioc 0 1) :=
    hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hIoi :
      IntegrableOn (fun t : ℝ => |Real.log t| ^ k * t ^ s * Real.exp (-b * t)) (Ioi 1) := by
    have hsk : -1 < s + k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hdom : IntegrableOn (fun t : ℝ => t ^ (s + k) * Real.exp (-b * t ^ (1 : ℝ))) (Ioi 1) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow hsk one_pos hb).mono_set (Ioi_subset_Ioi zero_le_one)
    refine hdom.mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlog_le : |Real.log t| ^ k ≤ t ^ k := by
      rw [abs_of_nonneg hlog_nn]
      exact pow_le_pow_left₀ hlog_nn (Real.log_le_self ht0.le) k
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_one]
    calc |Real.log t| ^ k * t ^ s * Real.exp (-b * t)
        ≤ t ^ k * t ^ s * Real.exp (-b * t) := by gcongr
      _ = t ^ (s + k) * Real.exp (-b * t) := by
          rw [← Real.rpow_natCast t k, ← Real.rpow_add ht0, add_comm (k : ℝ) s]
  exact (hIoc.union hIoi).mono_set fun t ht => by
    rcases le_or_gt t 1 with ht1 | ht1
    · exact Or.inl ⟨ht, ht1⟩
    · exact Or.inr ht1

namespace Complex

open MeasureTheory Set

/-- For `Re s > -1`, `Re w > 0`, and `k : ℕ`, `t ↦ t^s (log t)^k e^{-wt}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : -1 < s.re)
    (hw : 0 < w.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ s * (log t) ^ k * exp (-(w * t))) (Ioi 0) := by
  refine (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi hs hw k).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_log_pow_mul_exp_neg_mul s w k ht]

/-- For `Re s > 0` and `Re w > 0`, `t ↦ t^{s-1} e^{-wt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (Ioi 0) := by
  have hs' : -1 < (s - 1).re := by simp; linarith
  simpa using integrableOn_cpow_mul_log_pow_mul_exp_neg_mul_Ioi hs' hw 0

/-- On any compact subset `K` of `{p : ℂ × ℂ | -1 < p.1.re ∧ 0 < p.2.re}`, the weighted
Gamma-Laplace integrand `t^{p.1} (log t)^k e^{-p.2 t}` admits a single integrable real majorant
on `(0, ∞)`. -/
theorem _root_.IsCompact.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (hKs : ∀ p ∈ K, -1 < p.1.re)
    (hKw : ∀ p ∈ K, 0 < p.2.re) (k : ℕ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t > (0 : ℝ),
        ‖(t : ℂ) ^ p.1 * (log t) ^ k * exp (-(p.2 * t))‖ ≤ g t := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, integrableOn_zero, by simp⟩
  obtain ⟨p₁, hp₁, hmin_s⟩ := hK.exists_isMinOn hne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨p₂, hp₂, hmax_s⟩ := hK.exists_isMaxOn hne (continuous_re.comp continuous_fst).continuousOn
  obtain ⟨q, hq, hmin_w⟩ := hK.exists_isMinOn hne (continuous_re.comp continuous_snd).continuousOn
  refine ⟨fun t => |Real.log t| ^ k * t ^ p₁.1.re * Real.exp (-q.2.re * t) +
      |Real.log t| ^ k * t ^ p₂.1.re * Real.exp (-q.2.re * t),
    (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi (hKs p₁ hp₁) (hKw q hq) k).add
      (Real.integrableOn_abs_log_pow_mul_rpow_mul_exp_neg_mul_Ioi (hKs p₂ hp₂) (hKw q hq) k),
    fun p hp t ht => ?_⟩
  rw [norm_cpow_mul_log_pow_mul_exp_neg_mul p.1 p.2 k ht]
  have hexp : Real.exp (-p.2.re * t) ≤ Real.exp (-q.2.re * t) :=
    Real.exp_le_exp.mpr (by have : q.2.re ≤ p.2.re := hmin_w hp; nlinarith)
  rcases le_or_gt t 1 with ht1 | ht1
  · have hrp : t ^ p.1.re ≤ t ^ p₁.1.re := Real.rpow_le_rpow_of_exponent_ge ht ht1 (hmin_s hp)
    exact le_add_of_le_of_nonneg (by gcongr) (by positivity)
  · have hrp : t ^ p.1.re ≤ t ^ p₂.1.re := Real.rpow_le_rpow_of_exponent_le ht1.le (hmax_s hp)
    exact le_add_of_nonneg_of_le (by positivity) (by gcongr)

end Complex
