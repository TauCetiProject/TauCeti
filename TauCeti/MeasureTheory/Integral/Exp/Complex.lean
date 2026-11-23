/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
-/

public section

open MeasureTheory Set
open scoped Interval Nat

namespace TauCeti

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
    rw [smul_smul, ← Complex.exp_add]
    congr 2
    ring
  rw [heq]
  refine hf.bdd_smul 1 (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [hμ] with t ht
  rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht)

private theorem cexp_neg_mul_ofReal_pow_smul_eq {E : Type*} [MulAction ℂ E]
    (v : E) (s₀ s : ℂ) (t : ℝ) (k : ℕ) :
    Complex.exp (-s * t) • ((t : ℂ) ^ k • v) =
      (Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k) • (Complex.exp (-s₀ * t) • v) := by
  rw [smul_smul, smul_smul, mul_right_comm _ ((t : ℂ) ^ k), ← Complex.exp_add,
    show -(s - s₀) * t + -s₀ * t = -s * t by ring]

/-- Pointwise domination of a polynomial-weighted complex exponential kernel: for `s₀.re < s.re`,
`0 ≤ t`, and `k : ℕ`, `‖exp (-s * t) • ((t : ℂ) ^ k • v)‖` is bounded by
`(k! / (s.re - s₀.re) ^ k) * ‖exp (-s₀ * t) • v‖`. -/
theorem norm_cexp_neg_mul_ofReal_pow_smul_le {E : Type*} [NormedAddCommGroup E]
    [MulAction ℂ E] [NormSMulClass ℂ E] (v : E) {s₀ s : ℂ} (hs : s₀.re < s.re) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) :
    ‖Complex.exp (-s * t) • ((t : ℂ) ^ k • v)‖ ≤
      (k ! : ℝ) / (s.re - s₀.re) ^ k * ‖Complex.exp (-s₀ * t) • v‖ := by
  rw [cexp_neg_mul_ofReal_pow_smul_eq v s₀ s t k, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re, Complex.sub_re,
    norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, mul_comm]
  simpa only [neg_mul] using pow_mul_exp_neg_mul_le (sub_pos.mpr hs) ht k

/-- Strictly to the right of a point of convergence `s₀`, multiplying `f` by any natural power
`t ^ k` preserves integrability of `t ↦ exp (-s * t) • f t` for any measure `μ` supported on
`[0, ∞)`. -/
theorem integrable_cexp_neg_mul_ofReal_pow_smul_of_re_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} {s₀ s : ℂ} {μ : Measure ℝ}
    (hf : Integrable (fun t : ℝ ↦ Complex.exp (-s₀ * t) • f t) μ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hs : s₀.re < s.re) (k : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • ((t : ℂ) ^ k • f t)) μ := by
  refine (hf.norm.const_mul ((k ! : ℝ) / (s.re - s₀.re) ^ k)).mono' ?_ ?_
  · rw [funext fun t ↦ cexp_neg_mul_ofReal_pow_smul_eq (f t) s₀ s t k]
    exact (by fun_prop : Continuous fun t : ℝ ↦
      Complex.exp (-(s - s₀) * t) * (t : ℂ) ^ k).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  · filter_upwards [hμ] with t ht
    exact norm_cexp_neg_mul_ofReal_pow_smul_le (f t) hs ht k

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

end TauCeti
