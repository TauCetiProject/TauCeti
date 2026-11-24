/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Asymptotics.LaplaceMethod.Gaussian

/-!
# Laplace's method in several variables

Let `E` be a finite-dimensional real normed space of dimension `n` equipped with an additive Haar
measure `μ`, `B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ` a real-bilinear form, `c, γ > 0`, and `f : ℕ → E → ℂ`
a sequence of functions that are eventually `μ`-almost everywhere strongly measurable. Suppose
that `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` pointwise for every `v : E`, and that
`‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds eventually in `t` uniformly in `v`.

This file proves the four conclusions of multivariate Laplace's method:

* `TauCeti.mul_norm_sq_le_re_of_laplaceMethod` and
  `TauCeti.pos_re_bilinear_of_laplaceMethod`: for a single vector `v`, convergence
  `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-z)` under the rescaled majorant gives
  `γ * c * ‖v‖ ^ 2 ≤ z.re`; applied to `z = B v v` with `c, γ > 0` and `v ≠ 0`, this yields
  `0 < (B v v).re` (without finite-dimensionality or a measure);
* `TauCeti.eventually_integrable_of_laplaceMethod`: `f t` is `μ`-integrable for large `t`;
* `TauCeti.tendsto_rpow_mul_integral_of_laplaceMethod`: for any almost-everywhere pointwise
  rescaled limit `g : E → ℂ`, `t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, g v ∂μ`;
* `TauCeti.eventually_integral_ne_zero_of_laplaceMethod`: `∫ v, f t v ∂μ ≠ 0` for large `t`;
* `TauCeti.tendsto_integral_of_laplaceMethod`: the bundled theorem combining all four.

By the real-exponent Bernoulli inequality, for `γ * t ≥ p := n / 2 + 1` the rescaled majorant
`(1 + c * ‖(Real.sqrt t)⁻¹ • w‖ ^ 2) ^ (-(γ * t))` is dominated uniformly in `t` and `w` by
the `μ`-integrable envelope `(1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)`. Changing variables
`v = (Real.sqrt t)⁻¹ • w` and applying dominated convergence gives the Gaussian limit, which is
nonzero by `TauCeti.integral_cexp_neg_bilinear_ne_zero`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.7.
-/

public section

open Complex Filter MeasureTheory Topology

namespace TauCeti

private theorem tendsto_rescaled_norm_sq_majorant {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (c γ : ℝ) (v : E) :
    Tendsto (fun t : ℕ ↦ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t)))
      atTop (𝓝 (Real.exp (-(γ * c * ‖v‖ ^ 2)))) := by
  have h1 : Tendsto (fun t : ℕ ↦ (1 + c * ‖v‖ ^ 2 / (t : ℝ)) ^ t) atTop
      (𝓝 (Real.exp (c * ‖v‖ ^ 2))) :=
    Real.tendsto_one_add_div_pow_exp (c * ‖v‖ ^ 2)
  have h2 : Tendsto (fun t : ℕ ↦ ((1 + c * ‖v‖ ^ 2 / (t : ℝ)) ^ t) ^ (-γ)) atTop
      (𝓝 ((Real.exp (c * ‖v‖ ^ 2)) ^ (-γ))) :=
    h1.rpow_const (Or.inl (Real.exp_pos _).ne')
  have hval : (Real.exp (c * ‖v‖ ^ 2)) ^ (-γ) = Real.exp (-(γ * c * ‖v‖ ^ 2)) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [hval] at h2
  have hpos : ∀ᶠ t : ℕ in atTop, 0 < 1 + c * ‖v‖ ^ 2 / (t : ℝ) := by
    have ht0 : Tendsto (fun t : ℕ ↦ 1 + c * ‖v‖ ^ 2 / (t : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
    exact ht0.eventually (lt_mem_nhds zero_lt_one)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hpos] with t ht hbase
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hsq : ‖(Real.sqrt t)⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      inv_pow, Real.sq_sqrt htpos.le, div_eq_inv_mul]
  rw [hsq, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le,
    show (t : ℝ) * -γ = -(γ * t) by ring, mul_div_assoc]

private theorem rpow_neg_one_add_div_le {u p q : ℝ} (hu : 0 ≤ u) (hp : 0 < p) (hpq : p ≤ q) :
    (1 + u / q) ^ (-q) ≤ (1 + u / p) ^ (-p) := by
  have hq : 0 < q := hp.trans_le hpq
  have hqp : 1 ≤ q / p := (one_le_div hp).mpr hpq
  have hber : 1 + u / p ≤ (1 + u / q) ^ (q / p) := by
    have h := one_add_mul_self_le_rpow_one_add (div_nonneg hu hq.le |>.trans' (by linarith)) hqp
    refine le_trans (le_of_eq ?_) h
    field_simp
  have hpow : (1 + u / p) ^ p ≤ (1 + u / q) ^ q := by
    calc (1 + u / p) ^ p ≤ ((1 + u / q) ^ (q / p)) ^ p :=
          Real.rpow_le_rpow (by positivity) hber hp.le
      _ = (1 + u / q) ^ q := by
          rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ q hp.ne']
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) p) hpow

/-- **Pointwise lower bound via Laplace's method**: if `f t ((Real.sqrt t)⁻¹ • v)` converges to
`Complex.exp (-z)` and is eventually bounded by
`(1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))`, then `γ * c * ‖v‖ ^ 2 ≤ z.re`. -/
theorem mul_norm_sq_le_re_of_laplaceMethod {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {c γ : ℝ} {f : ℕ → E → ℂ} {v : E} {z : ℂ}
    (hlim : Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-z))))
    (hmaj : ∀ᶠ t in atTop,
      ‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))) :
    γ * c * ‖v‖ ^ 2 ≤ z.re := by
  have hnorm : Tendsto (fun t : ℕ ↦ ‖f t ((Real.sqrt t)⁻¹ • v)‖) atTop
      (𝓝 (Real.exp (-z.re))) := by
    simpa [Complex.norm_exp, Complex.neg_re] using hlim.norm
  have hle_exp : Real.exp (-z.re) ≤ Real.exp (-(γ * c * ‖v‖ ^ 2)) :=
    le_of_tendsto_of_tendsto hnorm (tendsto_rescaled_norm_sq_majorant c γ v) hmaj
  linarith [Real.exp_le_exp.mp hle_exp]

/-- **Positivity via Laplace's method** (7.1 (a)): if `c, γ > 0` and
`f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-z)` with
`‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))` eventually
for `v ≠ 0`, then `0 < z.re`. -/
theorem pos_re_of_laplaceMethod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) {f : ℕ → E → ℂ} {v : E} {z : ℂ} (hv : v ≠ 0)
    (hlim : Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-z))))
    (hmaj : ∀ᶠ t in atTop,
      ‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))) :
    0 < z.re := by
  have hpos : 0 < γ * c * ‖v‖ ^ 2 :=
    mul_pos (mul_pos hγ hc) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact hpos.trans_le (mul_norm_sq_le_re_of_laplaceMethod hlim hmaj)

/-- **Eventual integrability** in multivariate Laplace's method (7.1 (c)): if `f t` is eventually
`μ`-almost everywhere strongly measurable and bounded uniformly by `(1 + c * ‖v‖ ^ 2) ^ (-(γ * t))`
for `c, γ > 0`, then `f t` is `μ`-integrable for all sufficiently large `t`. -/
theorem eventually_integrable_of_laplaceMethod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) {f : ℕ → E → ℂ}
    (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hmaj : ∀ᶠ t in atTop, ∀ v : E, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t in atTop, Integrable (f t) μ := by
  have hdim : ∀ᶠ t : ℕ in atTop, (Module.finrank ℝ E : ℝ) < 2 * γ * (t : ℝ) := by
    have ht : Tendsto (fun t : ℕ ↦ 2 * γ * (t : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact ht.eventually_gt_atTop _
  filter_upwards [hf, hmaj, hdim] with t hft ht hdimt
  have hint : Integrable (fun v : E ↦ (1 + c * ‖v‖ ^ 2) ^ (-(2 * γ * t) / 2)) μ :=
    integrable_one_add_mul_norm_sq_rpow μ hc hdimt
  refine hint.mono' hft (.of_forall fun v ↦ ?_)
  calc ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t)) := ht v
    _ = (1 + c * ‖v‖ ^ 2) ^ (-(2 * γ * t) / 2) := by ring_nf

private theorem aEStronglyMeasurable_comp_inv_sqrt_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f : E → ℂ} (hf : AEStronglyMeasurable f μ) {t : ℕ} (ht : 1 ≤ t) :
    AEStronglyMeasurable (fun w : E ↦ f ((Real.sqrt t)⁻¹ • w)) μ := by
  have hne : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht)).ne'
  have hqmp : QuasiMeasurePreserving (fun w : E ↦ (Real.sqrt t)⁻¹ • w) μ μ := by
    refine ⟨(continuous_const_smul _).measurable.aemeasurable, ?_⟩
    rw [Measure.map_addHaar_smul μ hne]
    exact Measure.smul_absolutelyContinuous
  exact hf.comp_quasiMeasurePreserving hqmp

private theorem rescaled_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (g : E → ℂ) (t : ℕ) :
    ∫ w : E, g ((Real.sqrt t)⁻¹ • w) ∂μ =
      (((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v : E, g v ∂μ := by
  rw [Measure.integral_comp_inv_smul_of_nonneg μ g (Real.sqrt_nonneg _), Complex.real_smul]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg t)]
  ring_nf

/-- **Rescaled limit** in multivariate Laplace's method (7.1 (c)): if `f t` is eventually
`μ`-almost everywhere strongly measurable, `‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds
eventually and uniformly in `v`, and `f t ((Real.sqrt t)⁻¹ • v) → g v` for `μ`-almost every `v`,
then `t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, g v ∂μ` as `t → ∞`. -/
theorem tendsto_rpow_mul_integral_of_laplaceMethod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} {g : E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ᵐ v ∂μ, Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (g v)))
    (hmaj : ∀ᶠ t in atTop, ∀ v : E, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    Tendsto (fun t : ℕ ↦ (((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v, f t v ∂μ)
      atTop (𝓝 (∫ v, g v ∂μ)) := by
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2 + 1
  have hp : 0 < p := by positivity
  have hbound_int : Integrable (fun w : E ↦ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)) μ := by
    have hbase := integrable_one_add_mul_norm_sq_rpow μ (c := γ * c / p) (r := 2 * p)
      (by positivity) (by simp only [p]; linarith)
    refine hbase.congr (.of_forall fun w ↦ ?_)
    ring_nf
  have hmeas : ∀ᶠ t : ℕ in atTop,
      AEStronglyMeasurable (fun w : E ↦ f t ((Real.sqrt t)⁻¹ • w)) μ := by
    filter_upwards [hf, eventually_ge_atTop 1] with t hft ht
    exact aEStronglyMeasurable_comp_inv_sqrt_smul hft ht
  have hp_ev : ∀ᶠ t : ℕ in atTop, p ≤ γ * (t : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hγ).eventually_ge_atTop p
  have hdom : ∀ᶠ t : ℕ in atTop, ∀ᵐ w : E ∂μ,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p) := by
    filter_upwards [hmaj, eventually_ge_atTop 1, hp_ev] with t ht ht1 htp
    refine .of_forall fun w ↦ (ht _).trans ?_
    have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht1
    have hsq : c * ‖(Real.sqrt t)⁻¹ • w‖ ^ 2 = (γ * c * ‖w‖ ^ 2) / (γ * t) := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        inv_pow, Real.sq_sqrt htpos.le]
      field_simp [hγ.ne', htpos.ne']
    rw [hsq, show (γ * c / p) * ‖w‖ ^ 2 = (γ * c * ‖w‖ ^ 2) / p by ring]
    exact rpow_neg_one_add_div_le (by positivity) hp htp
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun w : E ↦ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)) hmeas hdom hbound_int hlim
  simpa only [rescaled_integral_eq] using hconv

/-- **Non-vanishing** in multivariate Laplace's method (7.1 (d)): for all sufficiently large `t`,
`∫ v, f t v ∂μ ≠ 0`. -/
theorem eventually_integral_ne_zero_of_laplaceMethod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ v : E,
      Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-B v v))))
    (hmaj : ∀ᶠ t in atTop, ∀ v : E, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t in atTop, ∫ v, f t v ∂μ ≠ 0 := by
  have hpos : ∀ v : E, v ≠ 0 → 0 < (B v v).re := fun v hv ↦
    pos_re_of_laplaceMethod hc hγ hv (hlim v) (hmaj.mono fun _ ht ↦ ht _)
  have hne : ∫ v : E, Complex.exp (-B v v) ∂μ ≠ 0 :=
    integral_cexp_neg_bilinear_ne_zero μ B hpos
  have hlim_int := tendsto_rpow_mul_integral_of_laplaceMethod μ hc hγ hf (.of_forall hlim) hmaj
  exact (hlim_int.eventually_ne hne).mono fun t ht hzero ↦ ht (by simp [hzero])

/-- **Laplace's method in several variables with a uniform majorant** (7.1 (a), (c), (d)):
if `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` pointwise for every `v : E`, and
`‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` eventually in `t` uniformly in `v`, then:
`(B v v).re > 0` for all `v ≠ 0`; `f t` is eventually `μ`-integrable;
`t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, Complex.exp (-B v v) ∂μ`; and eventually `∫ v, f t v ∂μ ≠ 0`. -/
theorem tendsto_integral_of_laplaceMethod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ v : E,
      Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-B v v))))
    (hmaj : ∀ᶠ t in atTop, ∀ v : E, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    (∀ v : E, v ≠ 0 → 0 < (B v v).re) ∧
      (∀ᶠ t in atTop, Integrable (f t) μ) ∧
      Tendsto (fun t : ℕ ↦ (((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v, f t v ∂μ)
        atTop (𝓝 (∫ v, Complex.exp (-B v v) ∂μ)) ∧
      ∀ᶠ t in atTop, ∫ v, f t v ∂μ ≠ 0 :=
  ⟨fun v hv ↦ pos_re_of_laplaceMethod hc hγ hv (hlim v) (hmaj.mono fun _ ht ↦ ht _),
    eventually_integrable_of_laplaceMethod μ hc hγ hf hmaj,
    tendsto_rpow_mul_integral_of_laplaceMethod μ hc hγ hf (.of_forall hlim) hmaj,
    eventually_integral_ne_zero_of_laplaceMethod μ B hc hγ hf hlim hmaj⟩

end TauCeti
