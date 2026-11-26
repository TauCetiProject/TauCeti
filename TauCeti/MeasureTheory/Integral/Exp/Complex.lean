/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Integrability and interval integrals with a complex exponential kernel

This file collects general integrability and interval-integral identities for functions weighted by
the complex exponential kernel `t ↦ Complex.exp (-s * t)`.

## Main results

* `TauCeti.integrable_cexp_neg_mul_smul_of_re_le`: for a measure supported on `[0, ∞)`,
  integrability of `t ↦ exp (-s₀ * t) • f t` implies integrability of `t ↦ exp (-s * t) • f t`
  whenever `s₀.re ≤ s.re`.
* `TauCeti.norm_cexp_neg_mul_ofReal_pow_smul_le` and
  `TauCeti.integrable_cexp_neg_mul_ofReal_pow_smul_of_re_lt`: pointwise domination and
  polynomial-moment integrability of `t ↦ exp (-s * t) • ((t : ℂ) ^ k • f t)` for `s₀.re < s.re`
  and a measure supported on `[0, ∞)`.
* `TauCeti.intervalIntegrable_cexp_neg_mul_smul_iff`: multiplying by `t ↦ exp (-s * t)` preserves
  `IntervalIntegrable` for vector-valued functions and arbitrary measures.
* `TauCeti.intervalIntegrable_of_integrableOn_cexp_neg_mul_smul_Ioi`: integrability of
  `t ↦ exp (-s * t) • g t` on `(a, ∞)` implies `IntervalIntegrable g μ a b` for all `b ≥ a`.
* `TauCeti.intervalIntegral_const_mul_cexp_neg_mul`:
  `∫ r in a..b, s * exp (-s * r) = exp (-s * a) - exp (-s * b)` for all `s : ℂ`, including `s = 0`.
* `TauCeti.intervalIntegral_ofReal_cpow_neg_sub_one`: substitution `x = exp t` identifying
  `∫ x in u..v, x ^ (-z - 1)` with `∫ t in log u..log v, exp (-z * t)` for `0 < u, v`.
-/

public section

open MeasureTheory Set
open scoped Interval Nat

namespace TauCeti

private theorem cexp_neg_mul_ofReal_pow_smul_eq {E : Type*} [MulAction ℂ E]
    (v : E) (s₀ s : ℂ) (t : ℝ) (k : ℕ) :
    Complex.exp (-s * t) • ((t : ℂ) ^ k • v) =
      (Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k) • (Complex.exp (-s₀ * t) • v) := by
  have hexp : -(s - s₀) * (t : ℂ) + -s₀ * (t : ℂ) = -s * (t : ℂ) := by ring
  rw [smul_smul, smul_smul, mul_right_comm _ ((t : ℂ) ^ k)]
  rw [← Complex.exp_add, hexp]

/-- If `t ↦ exp (-s₀ * t) • f t` is integrable with respect to a measure `μ` supported on
`[0, ∞)` (i.e. `0 ≤ t` `μ`-a.e.), then `t ↦ exp (-s * t) • f t` is also `μ`-integrable for
every `s` with `s₀.re ≤ s.re`. -/
theorem integrable_cexp_neg_mul_smul_of_re_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {s₀ s : ℂ} {μ : Measure ℝ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) μ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hs : s₀.re ≤ s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • f t) =
      fun t : ℝ ↦ Complex.exp (-(s - s₀) * t) • (Complex.exp (-s₀ * t) • f t) := by
    ext t
    simpa only [pow_zero, one_smul, mul_one] using cexp_neg_mul_ofReal_pow_smul_eq (f t) s₀ s t 0
  rw [heq]
  refine hf.bdd_smul 1 (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [hμ] with t ht
  rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re]
  simpa using exp_neg_sub_mul_le_of_le hs ht

private theorem norm_cexp_neg_mul_ofReal_pow_le {s₀ s : ℂ} (hs : s₀.re < s.re) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k‖ ≤ (k ! : ℝ) / (s.re - s₀.re) ^ k := by
  simpa [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, mul_comm (t ^ k) _] using
    pow_mul_exp_neg_mul_le (sub_pos.mpr hs) ht k

/-- Pointwise domination of a polynomial-weighted complex exponential kernel: for `s₀.re < s.re`,
`0 ≤ t`, and `k : ℕ`, `‖exp (-s * t) • ((t : ℂ) ^ k • v)‖` is bounded by
`(k! / (s.re - s₀.re) ^ k) * ‖exp (-s₀ * t) • v‖`. -/
theorem norm_cexp_neg_mul_ofReal_pow_smul_le {E : Type*} [NormedAddCommGroup E]
    [MulAction ℂ E] [NormSMulClass ℂ E] (v : E) {s₀ s : ℂ} (hs : s₀.re < s.re) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp (-s * t) • ((t : ℂ) ^ k • v)‖ ≤
      (k ! : ℝ) / (s.re - s₀.re) ^ k * ‖Complex.exp (-s₀ * t) • v‖ := by
  rw [cexp_neg_mul_ofReal_pow_smul_eq v s₀ s t k, norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_cexp_neg_mul_ofReal_pow_le hs ht k) (norm_nonneg _)

/-- Strictly to the right of a point of convergence `s₀`, multiplying `f` by any natural power
`t ^ k` preserves integrability of `t ↦ exp (-s * t) • f t` for any measure `μ` supported on
`[0, ∞)`. -/
theorem integrable_cexp_neg_mul_ofReal_pow_smul_of_re_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} {s₀ s : ℂ} {μ : Measure ℝ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) μ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hs : s₀.re < s.re) (k : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • ((t : ℂ) ^ k • f t)) μ := by
  have heq : (fun t : ℝ ↦ Complex.exp (-s * t) • ((t : ℂ) ^ k • f t)) =
      fun t : ℝ ↦ (Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k) •
        (Complex.exp (-s₀ * t) • f t) :=
    funext fun t ↦ cexp_neg_mul_ofReal_pow_smul_eq (f t) s₀ s t k
  rw [heq]
  refine hf.bdd_smul ((k ! : ℝ) / (s.re - s₀.re) ^ k)
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [hμ] with t ht
  exact norm_cexp_neg_mul_ofReal_pow_le hs ht k

/-- Multiplying by the scalar exponential `t ↦ exp (-s * t)` preserves `IntervalIntegrable` for
vector-valued functions with respect to any measure `μ`. -/
theorem intervalIntegrable_cexp_neg_mul_smul_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {a b : ℝ} {μ : Measure ℝ} (s : ℂ) :
    IntervalIntegrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) μ a b ↔
      IntervalIntegrable g μ a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.continuousOn_smul (by fun_prop)⟩
  have h' := h.continuousOn_smul (f := fun t : ℝ ↦ Complex.exp (s * t)) (by fun_prop)
  simpa only [smul_smul, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]
    using h'

/-- If `t ↦ exp (-s * t) • g t` is integrable on `(a, ∞)` with respect to `μ`, then `g` is
interval-integrable on `[a, b]` for every `b ≥ a`. -/
theorem intervalIntegrable_of_integrableOn_cexp_neg_mul_smul_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℝ → E} {s : ℂ} {a b : ℝ} {μ : Measure ℝ}
    (hg : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (Ioi a) μ) (hab : a ≤ b) :
    IntervalIntegrable g μ a b :=
  (intervalIntegrable_cexp_neg_mul_smul_iff s).mp
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hg.mono_set Ioc_subset_Ioi_self))

/-- For every `s : ℂ` and `a b : ℝ`,
`∫ r in a..b, s * exp (-s * r) = exp (-s * a) - exp (-s * b)`. -/
theorem intervalIntegral_const_mul_cexp_neg_mul (s : ℂ) (a b : ℝ) :
    ∫ r in a..b, s * Complex.exp (-s * r) =
      Complex.exp (-s * a) - Complex.exp (-s * b) := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hs)]
    field_simp [hs]
    ring

/-- **Substitution `x = exp t`.** For `0 < u` and `0 < v`, the integral of `x ^ (-z - 1)` over
`[u, v]` is the truncated Laplace transform `∫ t in log u..log v, exp (-z t)` of the constant
function `1`. -/
theorem intervalIntegral_ofReal_cpow_neg_sub_one {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (z : ℂ) :
    ∫ x in u..v, (x : ℂ) ^ (-z - 1) =
      ∫ t in Real.log u..Real.log v, Complex.exp (-z * t) := by
  have hg : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-z - 1))
      (Real.exp '' [[Real.log u, Real.log v]]) := by
    rintro _ ⟨t, -, rfl⟩
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (Real.exp_pos t).ne')).continuousWithinAt
  have h := intervalIntegral.integral_deriv_smul_comp' (fun t _ ↦ Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn hg
  rw [Real.exp_log hu, Real.exp_log hv] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [Function.comp_apply, Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'), ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  ring_nf

end TauCeti
