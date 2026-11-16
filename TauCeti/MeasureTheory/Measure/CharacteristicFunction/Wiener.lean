/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Decomposition.Atomic

/-!
# Wiener's lemma on the line

For a finite measure `σ` on `ℝ` with characteristic function `charFun σ t = ∫ exp(itξ) dσ(ξ)`,
the time averages of `|charFun σ t|²` converge to the sum of the squared masses of the atoms of
`σ` (`TauCeti.tendsto_average_norm_charFun_sq`, **Wiener's lemma**):

`T⁻¹ ∫₀ᵀ |charFun σ t|² dt → ∑' ξ, σ({ξ})²` as `T → ∞`.

In particular `σ` has no atoms exactly when these averages tend to `0`. This is the criterion
through which weak mixing of a measure-preserving flow is read off the spectral measures of its
Koopman group.

Two ingredients are of independent use.

* The twisted averages of a characteristic function recover its atoms
  (`TauCeti.tendsto_average_cexp_mul_charFun`): for every frequency `a`,
  `T⁻¹ ∫₀ᵀ exp(-iat) charFun ρ t dt → ρ({a})`. By Fubini the average is the integral against
  `ρ` of the kernel `T⁻¹ ∫₀ᵀ exp(it(ξ - a)) dt`, which is bounded by `1` and tends to the
  indicator of `{a}`.
* The squared modulus `charFun σ t * conj (charFun σ t)` is the characteristic function of the
  law of `ξ - η` under `σ ⊗ σ` (`TauCeti.charFun_map_prod_sub`), whose mass at `0` is the
  mass `∑' ξ, σ({ξ})²` of the diagonal.

## References

* M. Hochman, *Notes on ergodic theory* (2012), Proposition 6.6.3, for the analogue on the circle.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press
  (2004), Chapter I, §7, for Wiener's theorem on the Fourier–Stieltjes coefficients of a measure
  on the circle.
-/

public section

open Complex Filter MeasureTheory Topology Set
open scoped RealInnerProductSpace ComplexConjugate

namespace TauCeti

/-- The interval integral `∫₀ᵀ exp(itu) dt` has modulus at most `T`. -/
private lemma norm_integral_cexp_le (u : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, cexp (↑(t * u) * I)‖ ≤ T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
    (f := fun t ↦ cexp (↑(t * u) * I)) fun t _ ↦ (norm_exp_ofReal_mul_I _).le
  rwa [sub_zero, abs_of_nonneg hT, one_mul] at h

/-- For `u ≠ 0` the interval integral `∫₀ᵀ exp(itu) dt` has modulus at most `2 / |u|`,
uniformly in `T`. -/
private lemma norm_integral_cexp_le_of_ne_zero {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, cexp (↑(t * u) * I)‖ ≤ 2 / |u| := by
  have hc : (u : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hu) I_ne_zero
  have h : ∫ t in (0 : ℝ)..T, cexp (↑(t * u) * I) =
      (cexp (↑(T * u) * I) - 1) / (u * I) := by
    simp_rw [show ∀ t : ℝ, (↑(t * u) : ℂ) * I = u * I * t from fun t ↦ by push_cast; ring]
    rw [integral_exp_mul_complex hc, ofReal_zero, mul_zero, exp_zero]
  rw [h, norm_div, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  gcongr
  exact (norm_sub_le _ _).trans (by rw [norm_exp_ofReal_mul_I, norm_one]; norm_num)

/-- The averaged kernel `T⁻¹ ∫₀ᵀ exp(itu) dt` tends to `1` at `u = 0` and to `0` elsewhere. -/
private lemma tendsto_average_integral_cexp (u : ℝ) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, cexp (↑(t * u) * I)) atTop
      (𝓝 (({0} : Set ℝ).indicator 1 u)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with T hT
    simp [hT]
  · rw [indicator_of_notMem (by simpa using hu)]
    refine squeeze_zero_norm' ?_ ((tendsto_inv_atTop_zero.const_mul (2 / |u|)).trans
      (by rw [mul_zero]))
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg hT.le, mul_comm]
    gcongr
    exact norm_integral_cexp_le_of_ne_zero hu T

/-- **Atoms from twisted averages of a characteristic function.** For a finite measure `ρ` on `ℝ`
and a frequency `a`, the averages `T⁻¹ ∫₀ᵀ exp(-iat) charFun ρ t dt` converge to the mass
`ρ({a})` as `T → ∞`. -/
theorem tendsto_average_cexp_mul_charFun (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a : ℝ) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, cexp (-(a * t) * I) * charFun ρ t)
      atTop (𝓝 (ρ.real {a} : ℂ)) := by
  -- By Fubini, the average is the integral against `ρ` of the averaged kernel at `ξ - a`.
  have hcont : Continuous fun p : ℝ × ℝ ↦ cexp (↑(p.1 * (p.2 - a)) * I) := by fun_prop
  have hswap (T : ℝ) : (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, cexp (-(a * t) * I) * charFun ρ t =
      ∫ ξ, (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, cexp (↑(t * (ξ - a)) * I)) ∂ρ := by
    have : IsFiniteMeasure (volume.restrict (uIoc 0 T)) := by
      rw [uIoc]; infer_instance
    have hint : Integrable (Function.uncurry fun t ξ : ℝ ↦ cexp (↑(t * (ξ - a)) * I))
        ((volume.restrict (uIoc 0 T)).prod ρ) :=
      (integrable_const (1 : ℝ)).mono hcont.aestronglyMeasurable
        (ae_of_all _ fun p ↦ by rw [norm_one]; exact (norm_exp_ofReal_mul_I _).le)
    rw [integral_const_mul]
    congr 1
    refine (intervalIntegral.integral_congr fun t _ ↦ ?_).trans
      (intervalIntegral_integral_swap hint)
    rw [charFun_apply_real, ← integral_const_mul]
    congr 1 with ξ
    rw [← exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hswap]
  have hlim : ∫ ξ, ({0} : Set ℝ).indicator (1 : ℝ → ℂ) (ξ - a) ∂ρ = ρ.real {a} := by
    have : (fun ξ ↦ ({0} : Set ℝ).indicator (1 : ℝ → ℂ) (ξ - a)) =
        ({a} : Set ℝ).indicator fun _ ↦ 1 := by
      ext ξ
      simp [indicator_apply, sub_eq_zero]
    rw [this, integral_indicator_const _ (measurableSet_singleton a), real_smul, mul_one]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (μ := ρ) (fun _ ↦ 1) ?_ ?_
    (integrable_const 1) (ae_of_all _ fun ξ ↦ tendsto_average_integral_cexp (ξ - a))
  · exact Eventually.of_forall fun T ↦ (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun ξ t ↦ cexp (↑(t * (ξ - a)) * I)) (by fun_prop) 0 T)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop 0] with T hT
    refine ae_of_all _ fun ξ ↦ ?_
    rw [norm_mul, norm_inv, norm_real, Real.norm_of_nonneg hT.le, inv_mul_le_one₀ hT]
    exact norm_integral_cexp_le _ hT.le

/-- The characteristic function of the law of `x - y` under `μ ⊗ ν` is
`charFun μ t * conj (charFun ν t)`. For `ν = μ` it is the squared modulus of `charFun μ t`. -/
theorem charFun_map_prod_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSub₂ E]
    (μ ν : Measure E) [SFinite μ] [SFinite ν] (t : E) :
    charFun ((μ.prod ν).map fun p ↦ p.1 - p.2) t = charFun μ t * conj (charFun ν t) := by
  rw [← charFun_neg, charFun_apply,
    integral_map measurable_sub.aemeasurable (by fun_prop : Continuous _).aestronglyMeasurable]
  simp_rw [charFun_apply, ← integral_prod_mul, inner_sub_left, inner_neg_right, ← exp_add]
  congr 1 with p
  push_cast
  ring_nf

/-- **Wiener's lemma** on the line: for a finite measure `σ` on `ℝ`, the time averages
`T⁻¹ ∫₀ᵀ |charFun σ t|² dt` of the squared modulus of its characteristic function converge, as
`T → ∞`, to the sum `∑' ξ, σ({ξ})²` of the squared masses of its atoms. All but countably many
terms of the sum vanish. -/
theorem tendsto_average_norm_charFun_sq (σ : Measure ℝ) [IsFiniteMeasure σ] :
    Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖charFun σ t‖ ^ 2)
      atTop (𝓝 (∑' ξ : ℝ, σ.real {ξ} ^ 2)) := by
  set ρ := (σ.prod σ).map fun p : ℝ × ℝ ↦ p.1 - p.2
  -- `ρ` gives the point `0`, that is the diagonal of `σ ⊗ σ`, the mass `∑' ξ, σ({ξ})²`.
  have hρ : ρ.real {0} = ∑' ξ : ℝ, σ.real {ξ} ^ 2 := by
    have hS : MeasurableSet ((fun p : ℝ × ℝ ↦ p.1 - p.2) ⁻¹' {0}) :=
      measurable_sub (measurableSet_singleton 0)
    have h0 : ρ {0} = ∑' ξ, σ {ξ} ^ 2 := by
      rw [Measure.map_apply measurable_sub (measurableSet_singleton 0), Measure.prod_apply hS]
      simp_rw [sq, ← Measure.lintegral_measure_singleton]
      congr 1 with x
      congr 1 with y
      simp [sub_eq_zero, eq_comm]
    rw [measureReal_def, h0, ENNReal.tsum_toReal_eq fun ξ ↦ by finiteness]
    simp [measureReal_def]
  have h := (continuous_re.tendsto _).comp (tendsto_average_cexp_mul_charFun ρ 0)
  rw [← hρ]
  refine h.congr fun T ↦ ?_
  simp only [Function.comp_apply, ofReal_zero, zero_mul, neg_zero, exp_zero, one_mul]
  simp_rw [ρ, charFun_map_prod_sub, mul_conj', ← ofReal_pow, intervalIntegral.integral_ofReal,
    ← ofReal_inv, ← ofReal_mul, ofReal_re]

end TauCeti
