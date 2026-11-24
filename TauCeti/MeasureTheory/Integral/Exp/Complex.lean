/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrability and interval integrals with a complex exponential kernel

This file collects general integrability and interval-integral identities for functions weighted by
the complex exponential kernel `t ↦ Complex.exp (-s * t)`.

## Main results

* `TauCeti.integrable_cexp_neg_mul_smul_of_re_le`: for a measure supported on `[0, ∞)`,
  integrability of `t ↦ exp (-s₀ * t) • f t` implies integrability of `t ↦ exp (-s * t) • f t`
  whenever `s₀.re ≤ s.re`.
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
open scoped Interval

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
