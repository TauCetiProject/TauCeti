/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.norm_inv_mul_integral_cexp_mul_I_le_one` and
  `TauCeti.tendsto_inv_mul_integral_cexp_mul_I`: uniform bound `≤ 1` and pointwise limit as
  `T → ∞` for the exponential averaging kernel `(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (t * u * I)`.
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

/-- The exponential averaging kernel `(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (t * u * I)` has norm at
most `1` for every real frequency `u` and every `T : ℝ`. -/
theorem norm_inv_mul_integral_cexp_mul_I_le_one (u T : ℝ) :
    ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I)‖ ≤ 1 := by
  by_cases hT : T = 0
  · simp [hT]
  have hnorm : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖Complex.exp (t * u * Complex.I)‖ ≤ 1 := fun t _ ↦ by
    rw [Complex.norm_exp]
    simp
  calc ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I)‖
      = |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |T|⁻¹ * (1 * |T - 0|) := by
        gcongr
        exact intervalIntegral.norm_integral_le_of_norm_le_const hnorm
    _ = 1 := by
        rw [sub_zero, one_mul, inv_mul_cancel₀ (abs_ne_zero.mpr hT)]

open Filter in
open scoped Topology in
/-- The exponential averaging kernel `(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, exp (t * u * I)` converges to
`1` at `u = 0` and to `0` for `u ≠ 0` as `T → ∞`. -/
theorem tendsto_inv_mul_integral_cexp_mul_I (u : ℝ) :
    Tendsto (fun T : ℝ ↦ (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * u * Complex.I))
      atTop (𝓝 (if u = 0 then (1 : ℂ) else 0)) := by
  split_ifs with hu
  · subst hu
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp [Complex.real_smul, hT.ne']
  · have hc : (u : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) Complex.I_ne_zero
    have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * (2 / |u|)) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const (2 / |u|)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have heq : (fun t : ℝ ↦ Complex.exp (t * u * Complex.I)) =
        fun t : ℝ ↦ Complex.exp (((u : ℂ) * Complex.I) * t) := by
      funext t
      congr 1
      ring
    have hnorm (x : ℝ) : ‖Complex.exp ((u : ℂ) * Complex.I * x)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [heq, integral_exp_mul_complex hc, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hT.le, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    gcongr
    calc ‖Complex.exp ((u : ℂ) * Complex.I * T) - Complex.exp ((u : ℂ) * Complex.I * (0 : ℝ))‖
        ≤ ‖Complex.exp ((u : ℂ) * Complex.I * T)‖ +
          ‖Complex.exp ((u : ℂ) * Complex.I * (0 : ℝ))‖ := norm_sub_le _ _
      _ = 2 := by
          rw [hnorm T, hnorm 0]
          norm_num

end TauCeti
