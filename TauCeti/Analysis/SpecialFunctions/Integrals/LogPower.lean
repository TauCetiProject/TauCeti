/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Moments of powers against logarithmic powers on `(0, 1]`

For `r > -1` and `k : ℕ`, the logarithmic moment integral on `(0, 1]` evaluates to
`∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)`. After the substitution `t = exp (-u)`
this is the rescaled Euler Gamma integral `∫_{u > 0} u ^ k * exp (-(r + 1) u) du`, and directly on
`(0, 1)` it follows by `k`-fold integration by parts from the primitive
`t ↦ t ^ (r + 1) / (r + 1) * (-log t) ^ (k + 1)`, whose boundary limits vanish at both endpoints
`0` and `1` (`TauCeti.tendsto_rpow_mul_neg_log_pow_nhdsGT_zero`).

These moments arise whenever a Taylor series in `t` is integrated against a logarithmic radial
kernel `(-log t) ^ k / t`, such as in the passage between the radial-integral and power-series
representations of the classical polylogarithms.

## Main declarations

* `TauCeti.locallyIntegrable_rpow_mul_log_pow`, `TauCeti.intervalIntegrable_rpow_mul_log_pow`, and
  `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`: local and interval integrability for `r > -1`.
* `TauCeti.integral_rpow_mul_neg_log_pow` and `TauCeti.integral_rpow_mul_log_pow`:
  `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)` and its signed counterpart for
  `r > -1`.
* `TauCeti.integral_pow_mul_neg_log_pow`, `TauCeti.integral_pow_mul_log_pow`,
  `TauCeti.integral_neg_log_pow`, and `TauCeti.integral_log_pow`: specializations to natural-number
  exponents `t ^ n` and to `n = 0`.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- On `ℝ` with Lebesgue measure, `t ↦ t ^ r * (log t) ^ k` is locally integrable for every
`r > -1` and `k : ℕ`. -/
theorem locallyIntegrable_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    LocallyIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume := by
  -- Split the exponent as `r = (r - 1) / 2 + (r + 1) / 2`: the second factor absorbs `|log t| ^ k`
  -- continuously at `0`, while the first factor `|t| ^ ((r - 1) / 2)` is locally integrable.
  set g : ℝ → ℝ := fun t ↦ if t = 0 then 0 else |t| ^ ((r + 1) / 2) * |Real.log t| ^ k
  have hg_cont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hg0 : g 0 = 0 := by simp [g]
      rw [continuousAt_iff_punctured_nhds, hg0]
      have h0 : Tendsto (fun t : ℝ ↦ |t ^ ((r + 1) / 2) * Real.log t ^ k|) (𝓝[>] 0) (𝓝 0) := by
        simpa using (tendsto_rpow_mul_log_pow_nhdsGT_zero (r := (r + 1) / 2)
          (by linarith) k).abs
      refine (h0.comp tendsto_abs_nhdsNE_zero).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
      have htabs : 0 < |t| := abs_pos.2 ht
      simp [g, ht, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htabs _), Real.log_abs]
    · have hcont : ContinuousAt (fun t : ℝ ↦ |t| ^ ((r + 1) / 2) * |Real.log t| ^ k) x := by
        refine (ContinuousAt.rpow_const continuous_abs.continuousAt (Or.inl (abs_ne_zero.2 hx))).mul
          ((Real.continuousAt_log hx).abs.pow k)
      refine hcont.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hx] with t ht
      simp [g, ht]
  have hbase : LocallyIntegrable (fun t : ℝ ↦ |t| ^ ((r - 1) / 2)) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := (1 - r) / 2)
      (by simp) (by simp; linarith) (.of_forall fun t ↦ ?_)
      (by fun_prop : Measurable _).aestronglyMeasurable
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), Real.norm_eq_abs, one_mul]
    exact le_of_eq (by congr 1; ring)
  refine (hbase.mul_continuous hg_cont).mono
    (by fun_prop : Measurable fun t : ℝ ↦ t ^ r * Real.log t ^ k).aestronglyMeasurable ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with t (ht : t ≠ 0)
  have htabs : 0 < |t| := abs_pos.2 ht
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.norm_eq_abs]
  simp only [g, ht, ↓reduceIte]
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg htabs.le _)
    (mul_nonneg (Real.rpow_nonneg htabs.le _) (pow_nonneg (abs_nonneg _) _))),
    ← mul_assoc, ← Real.rpow_add htabs]
  have hexp : (r - 1) / 2 + (r + 1) / 2 = r := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right (Real.abs_rpow_le_abs_rpow t r) (pow_nonneg (abs_nonneg _) k)

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (log t) ^ k` is interval integrable on every interval. -/
theorem intervalIntegrable_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * Real.log t ^ k) volume a b :=
  ((locallyIntegrable_rpow_mul_log_pow hr k).integrableOn_isCompact
    (isCompact_uIcc (a := a) (b := b))).intervalIntegrable

/-- For `r > -1` and `k : ℕ`, `t ↦ t ^ r * (-log t) ^ k` is interval integrable on every
interval. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) {a b : ℝ} :
    IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-Real.log t) ^ k) volume a b := by
  have h := (intervalIntegrable_rpow_mul_log_pow hr k (a := a) (b := b)).const_mul ((-1 : ℝ) ^ k)
  refine h.congr fun t _ ↦ ?_
  rw [neg_eq_neg_one_mul (Real.log t), mul_pow]
  ring

/-- Derivative of the integration-by-parts primitive
`t ↦ t ^ (r + 1) / (r + 1) * (-log t) ^ (k + 1)` at any nonzero `t`. -/
private lemma hasDerivAt_rpow_div_mul_neg_log_pow {r : ℝ} (hr1 : r + 1 ≠ 0) (k : ℕ)
    {t : ℝ} (ht0 : t ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ s ^ (r + 1) / (r + 1) * (-Real.log s) ^ (k + 1))
      (t ^ r * (-Real.log t) ^ (k + 1) -
        (k + 1 : ℝ) / (r + 1) * (t ^ r * (-Real.log t) ^ k)) t := by
  have hd1 : HasDerivAt (fun s : ℝ ↦ s ^ (r + 1) / (r + 1)) (t ^ r) t := by
    convert (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl ht0)).div_const (r + 1) using 1
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hr1]
  have hd2 : HasDerivAt (fun s : ℝ ↦ (-Real.log s) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (-Real.log t) ^ k * -t⁻¹) t :=
    ((Real.hasDerivAt_log ht0).fun_neg).fun_pow (k + 1)
  convert hd1.mul hd2 using 1
  push_cast
  have htr : t ^ (r + 1) * t⁻¹ = t ^ r := by
    rw [Real.rpow_add_one ht0, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
  calc t ^ r * (-Real.log t) ^ (k + 1) - (k + 1 : ℝ) / (r + 1) * (t ^ r * (-Real.log t) ^ k)
      = t ^ r * (-Real.log t) ^ (k + 1) -
          (k + 1 : ℝ) / (r + 1) * ((t ^ (r + 1) * t⁻¹) * (-Real.log t) ^ k) := by rw [htr]
    _ = t ^ r * (-Real.log t) ^ (k + 1) +
          t ^ (r + 1) / (r + 1) * (((k + 1 : ℝ) * (-Real.log t) ^ k) * -t⁻¹) := by ring

/-- For `r > -1` and `k : ℕ`, `∫ t in 0..1, t ^ r * (-log t) ^ k = k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ r * (-Real.log t) ^ k) = (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hr1 : 0 < r + 1 := by linarith
  induction k with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow hr1.ne', sub_zero]
  | succ k ih =>
    set F : ℝ → ℝ := fun t ↦ t ^ (r + 1) / (r + 1) * (-Real.log t) ^ (k + 1)
    have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F
        (t ^ r * (-Real.log t) ^ (k + 1) -
          (k + 1 : ℝ) / (r + 1) * (t ^ r * (-Real.log t) ^ k)) t :=
      fun _ ht ↦ hasDerivAt_rpow_div_mul_neg_log_pow hr1.ne' k ht.1.ne'
    have hint1 : IntervalIntegrable (fun t : ℝ ↦ t ^ r * (-Real.log t) ^ (k + 1)) volume 0 1 :=
      intervalIntegrable_rpow_mul_neg_log_pow hr (k + 1)
    have hint0 : IntervalIntegrable
        (fun t : ℝ ↦ (k + 1 : ℝ) / (r + 1) * (t ^ r * (-Real.log t) ^ k)) volume 0 1 :=
      (intervalIntegrable_rpow_mul_neg_log_pow hr k).const_mul _
    have hlim0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
      have h := (tendsto_rpow_mul_neg_log_pow_nhdsGT_zero hr1 (k + 1)).div_const (r + 1)
      rw [zero_div] at h
      refine h.congr' (.of_forall fun t ↦ ?_)
      dsimp only [F]
      ring
    have hlim1 : Tendsto F (𝓝[<] 1) (𝓝 0) := by
      have hcont : ContinuousAt F 1 := by
        refine ((Real.continuousAt_rpow_const 1 (r + 1) (Or.inl one_ne_zero)).div_const
          (r + 1)).mul (((Real.continuousAt_log one_ne_zero).neg).pow (k + 1))
      have hF1 : F 1 = 0 := by simp [F]
      exact hF1 ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
      hderiv (hint1.sub hint0) hlim0 hlim1
    rw [sub_zero, intervalIntegral.integral_sub hint1 hint0,
      intervalIntegral.integral_const_mul, sub_eq_zero] at hftc
    rw [hftc, ih, Nat.factorial_succ]
    push_cast
    rw [pow_succ (r + 1) (k + 1)]
    field_simp [hr1.ne']

/-- For `r > -1` and `k : ℕ`,
`∫ t in 0..1, t ^ r * (log t) ^ k = (-1) ^ k * k! / (r + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_log_pow {r : ℝ} (hr : -1 < r) (k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ r * Real.log t ^ k) =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) / (r + 1) ^ (k + 1) := by
  have hcongr : (∫ t : ℝ in 0..1, t ^ r * Real.log t ^ k) =
      (-1 : ℝ) ^ k * ∫ t : ℝ in 0..1, t ^ r * (-Real.log t) ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [← mul_assoc, mul_comm ((-1 : ℝ) ^ k) (t ^ r), mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  rw [hcongr, integral_rpow_mul_neg_log_pow hr k, mul_div_assoc]

/-- Natural-exponent specialization:
`∫ t in 0..1, t ^ n * (-log t) ^ k = k! / (n + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (n k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ n * (-Real.log t) ^ k) =
      (k.factorial : ℝ) / ((n : ℝ) + 1) ^ (k + 1) := by
  simpa [Real.rpow_natCast] using
    integral_rpow_mul_neg_log_pow (r := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n]) k

/-- Natural-exponent specialization:
`∫ t in 0..1, t ^ n * (log t) ^ k = (-1) ^ k * k! / (n + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_log_pow (n k : ℕ) :
    (∫ t : ℝ in 0..1, t ^ n * Real.log t ^ k) =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) / ((n : ℝ) + 1) ^ (k + 1) := by
  simpa [Real.rpow_natCast] using
    integral_rpow_mul_log_pow (r := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n]) k

/-- Pure logarithmic moment: `∫ t in 0..1, (-log t) ^ k = k!`. -/
theorem integral_neg_log_pow (k : ℕ) :
    (∫ t : ℝ in 0..1, (-Real.log t) ^ k) = (k.factorial : ℝ) := by
  simpa using integral_pow_mul_neg_log_pow 0 k

/-- Signed pure logarithmic moment: `∫ t in 0..1, (log t) ^ k = (-1) ^ k * k!`. -/
theorem integral_log_pow (k : ℕ) :
    (∫ t : ℝ in 0..1, Real.log t ^ k) = (-1 : ℝ) ^ k * (k.factorial : ℝ) := by
  simpa using integral_pow_mul_log_pow 0 k

end TauCeti
