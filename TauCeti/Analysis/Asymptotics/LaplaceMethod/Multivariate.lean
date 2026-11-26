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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Bilinear
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Laplace's method in several variables

Let `E` be a finite-dimensional real normed space of dimension `n` equipped with an additive Haar
measure `μ`, `B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ` a real-bilinear form, `c, γ > 0`, and `f : ℕ → E → ℂ`
a sequence of functions that are eventually `μ`-almost everywhere strongly measurable. Suppose
that `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` for `μ`-almost every `v : E`, and that
`‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds for `μ`-almost every `v : E` when `t` is large.

This file proves the four conclusions of multivariate Laplace's method:

* `TauCeti.re_pos_of_laplaceMethod_of_ae`: `0 < (B v v).re` for every `v ≠ 0`;
* `TauCeti.eventually_integrable_of_laplaceMethod`: `f t` is `μ`-integrable for large `t`;
* `TauCeti.tendsto_rpow_mul_integral_of_laplaceMethod`: for any almost-everywhere pointwise
  rescaled limit `g : E → ℂ`, `t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, g v ∂μ`;
* `TauCeti.eventually_integral_ne_zero_of_laplaceMethod`: `∫ v, f t v ∂μ ≠ 0` for large `t`.

`TauCeti.laplaceMethod_multivariate` bundles these four statements for `g v = Complex.exp (-B v v)`.

The pointwise ingredients are `TauCeti.mul_norm_sq_le_re_of_laplaceMethod` and
`TauCeti.re_pos_of_laplaceMethod`: for a single vector `v`, convergence
`f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-z)` under the rescaled majorant gives
`γ * c * ‖v‖ ^ 2 ≤ z.re`; applied to `z = B v v` with `c, γ > 0` and `v ≠ 0`, this yields
`0 < (B v v).re` (without finite-dimensionality or a measure).

By the real-exponent Bernoulli inequality (`TauCeti.rpow_neg_one_add_div_le`), for
`γ * t ≥ p := n / 2 + 1` the rescaled majorant `(1 + c * ‖(Real.sqrt t)⁻¹ • w‖ ^ 2) ^ (-(γ * t))`
is dominated `μ`-almost everywhere by the `μ`-integrable envelope
`(1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)` (`TauCeti.integrable_rpow_neg_one_add_mul_norm_sq`). Changing
variables `v = (Real.sqrt t)⁻¹ • w` and applying dominated convergence gives the Gaussian limit,
whose strict diagonal positivity on nonzero vectors follows from the almost-everywhere inequality
by continuity and is nonzero by `TauCeti.integral_cexp_neg_bilinear_ne_zero`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.7.
* Levent Alpöge's prior formalization
  (`ReciprocityTheory.ChartRestriction.DS.Lap.Base.GaussianLimitHaar`).
-/

public section

open Complex Filter MeasureTheory Module Topology

namespace TauCeti

private theorem inv_sqrt_natCast_ne_zero {t : ℕ} (ht : 1 ≤ t) : (Real.sqrt t)⁻¹ ≠ 0 :=
  inv_ne_zero (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht)).ne'

private theorem tendsto_rescaled_norm_sq_majorant {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (c γ : ℝ) (v : E) :
    Tendsto (fun t : ℕ ↦ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t)))
      atTop (𝓝 (Real.exp (-(γ * c * ‖v‖ ^ 2)))) := by
  have h1 := (Real.tendsto_one_add_div_rpow_mul_exp (c * ‖v‖ ^ 2) (-γ)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Real.exp (c * ‖v‖ ^ 2 * -γ) = Real.exp (-(γ * c * ‖v‖ ^ 2)) := by ring_nf
  rw [hlim] at h1
  refine h1.congr' (.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply]
  rw [TauCeti.norm_inv_sqrt_smul_sq (Nat.cast_nonneg t) v, mul_div_assoc, neg_mul]

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

/-- **Positivity via Laplace's method**: if `c, γ > 0` and
`f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-z)` with
`‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))` eventually
for `v ≠ 0`, then `0 < z.re`. -/
theorem re_pos_of_laplaceMethod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) {f : ℕ → E → ℂ} {v : E} {z : ℂ} (hv : v ≠ 0)
    (hlim : Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-z))))
    (hmaj : ∀ᶠ t in atTop,
      ‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t))) :
    0 < z.re := by
  have hpos : 0 < γ * c * ‖v‖ ^ 2 :=
    mul_pos (mul_pos hγ hc) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  exact hpos.trans_le (mul_norm_sq_le_re_of_laplaceMethod hlim hmaj)

/-- **Eventual integrability** in multivariate Laplace's method: if `c, γ > 0`, `f t` is
eventually `μ`-almost everywhere strongly measurable, and
`‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds for `μ`-almost every `v` for all large `t`,
then `f t` is `μ`-integrable for all sufficiently large `t`. -/
theorem eventually_integrable_of_laplaceMethod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) {f : ℕ → E → ℂ}
    (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hmaj : ∀ᶠ t in atTop, ∀ᵐ v ∂μ, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t in atTop, Integrable (f t) μ := by
  have hdim : ∀ᶠ t : ℕ in atTop, (finrank ℝ E : ℝ) < 2 * γ * (t : ℝ) := by
    have ht : Tendsto (fun t : ℕ ↦ 2 * γ * (t : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact ht.eventually_gt_atTop _
  filter_upwards [hf, hmaj, hdim] with t hft ht hdimt
  have hint : Integrable (fun v : E ↦ (1 + c * ‖v‖ ^ 2) ^ (-(2 * γ * t) / 2)) μ :=
    integrable_rpow_neg_one_add_mul_norm_sq μ hc hdimt
  refine hint.mono' hft ?_
  filter_upwards [ht] with v hv
  have hexp : -(γ * (t : ℝ)) = -(2 * γ * t) / 2 := by ring
  exact hv.trans_eq (by rw [hexp])

private theorem rescaled_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (g : E → ℂ) (t : ℕ) :
    ∫ w : E, g ((Real.sqrt t)⁻¹ • w) ∂μ =
      (((t : ℝ) ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v : E, g v ∂μ := by
  rw [Measure.integral_comp_inv_smul_of_nonneg μ g (Real.sqrt_nonneg _), Complex.real_smul]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg t)]
  ring_nf

/-- **Rescaled limit** in multivariate Laplace's method: if `c, γ > 0`, `f t` is eventually
`μ`-almost everywhere strongly measurable, `‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds
eventually for `μ`-almost every `v`, and `f t ((Real.sqrt t)⁻¹ • v) → g v` for `μ`-almost
every `v`, then `t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, g v ∂μ` as `t → ∞`. -/
theorem tendsto_rpow_mul_integral_of_laplaceMethod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} {g : E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ᵐ v ∂μ, Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (g v)))
    (hmaj : ∀ᶠ t in atTop, ∀ᵐ v ∂μ, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    Tendsto (fun t : ℕ ↦ (((t : ℝ) ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v, f t v ∂μ)
      atTop (𝓝 (∫ v, g v ∂μ)) := by
  set p : ℝ := (finrank ℝ E : ℝ) / 2 + 1
  have hp : 0 < p := by positivity
  have hbound_int : Integrable (fun w : E ↦ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)) μ := by
    have hbase := integrable_rpow_neg_one_add_mul_norm_sq μ (c := γ * c / p) (r := 2 * p)
      (by positivity) (by simp only [p]; linarith)
    refine hbase.congr (.of_forall fun w ↦ ?_)
    have hexp : -(2 * p) / 2 = -p := by ring
    rw [hexp]
  have hmeas : ∀ᶠ t : ℕ in atTop,
      AEStronglyMeasurable (fun w : E ↦ f t ((Real.sqrt t)⁻¹ • w)) μ := by
    filter_upwards [hf, eventually_ge_atTop 1] with t hft ht
    exact hft.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul μ (inv_sqrt_natCast_ne_zero ht))
  have hp_ev : ∀ᶠ t : ℕ in atTop, p ≤ γ * (t : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hγ).eventually_ge_atTop p
  have hdom : ∀ᶠ t : ℕ in atTop, ∀ᵐ w : E ∂μ,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p) := by
    filter_upwards [hmaj, eventually_ge_atTop 1, hp_ev] with t ht ht1 htp
    have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht1
    filter_upwards
      [(Measure.quasiMeasurePreserving_smul μ (inv_sqrt_natCast_ne_zero ht1)).ae ht] with w hw
    have hmul : c * (‖w‖ ^ 2 / t) = (γ * c * ‖w‖ ^ 2) / (γ * t) := by
      field_simp [hγ.ne', htpos.ne']
    have hcoef : (γ * c / p) * ‖w‖ ^ 2 = (γ * c * ‖w‖ ^ 2) / p := by ring
    refine hw.trans ?_
    rw [TauCeti.norm_inv_sqrt_smul_sq (Nat.cast_nonneg t) w, hmul, hcoef]
    exact rpow_neg_one_add_div_le (by positivity) hp htp
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun w : E ↦ (1 + (γ * c / p) * ‖w‖ ^ 2) ^ (-p)) hmeas hdom hbound_int hlim
  simpa only [rescaled_integral_eq] using hconv

/-- **Positivity** in multivariate Laplace's method: if `c, γ > 0`,
`f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` for `μ`-almost every `v`, and
`‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds eventually for `μ`-almost every `v`, then
`0 < (B v v).re` for every `v ≠ 0`. -/
theorem re_pos_of_laplaceMethod_of_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ}
    (hlim : ∀ᵐ v ∂μ,
      Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-B v v))))
    (hmaj : ∀ᶠ t in atTop, ∀ᵐ v ∂μ, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ v : E, v ≠ 0 → 0 < (B v v).re := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hmaj.and (eventually_ge_atTop 1))
  have hmaj_all : ∀ t : ℕ, ∀ᵐ v ∂μ, T ≤ t →
      ‖f t ((Real.sqrt t)⁻¹ • v)‖ ≤ (1 + c * ‖(Real.sqrt t)⁻¹ • v‖ ^ 2) ^ (-(γ * t)) := by
    intro t
    by_cases ht : T ≤ t
    · exact ((Measure.quasiMeasurePreserving_smul μ
        (inv_sqrt_natCast_ne_zero (hT t ht).2)).ae (hT t ht).1).mono fun _ hv _ ↦ hv
    · exact .of_forall fun _ hle ↦ (ht hle).elim
  have hae : ∀ᵐ v ∂μ, γ * c * ‖v‖ ^ 2 ≤ (B v v).re := by
    filter_upwards [hlim, ae_all_iff.mpr hmaj_all] with v hv_lim hv_maj
    exact mul_norm_sq_le_re_of_laplaceMethod hv_lim (eventually_atTop.mpr ⟨T, hv_maj⟩)
  have hcont_l : Continuous fun v : E ↦ γ * c * ‖v‖ ^ 2 :=
    continuous_const.mul (continuous_norm.pow 2)
  have hcont_r : Continuous fun v : E ↦ (B v v).re :=
    Complex.continuous_re.comp B.continuous_apply_self
  have hle : ∀ v : E, γ * c * ‖v‖ ^ 2 ≤ (B v v).re :=
    (Continuous.ae_le_iff_le μ hcont_l hcont_r).mp hae
  intro v hv
  exact (mul_pos (mul_pos hγ hc) (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hle v)

/-- **Non-vanishing** in multivariate Laplace's method: if `c, γ > 0`, `f t` is eventually
`μ`-almost everywhere strongly measurable, `‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds
eventually for `μ`-almost every `v`, and `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` for
`μ`-almost every `v`, then `∫ v, f t v ∂μ ≠ 0` for all sufficiently large `t`. -/
theorem eventually_integral_ne_zero_of_laplaceMethod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ᵐ v ∂μ,
      Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-B v v))))
    (hmaj : ∀ᶠ t in atTop, ∀ᵐ v ∂μ, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t in atTop, ∫ v, f t v ∂μ ≠ 0 := by
  have hpos := re_pos_of_laplaceMethod_of_ae μ B hc hγ hlim hmaj
  have hne : ∫ v : E, Complex.exp (-B v v) ∂μ ≠ 0 := integral_cexp_neg_bilinear_ne_zero μ B hpos
  have hlim_int := tendsto_rpow_mul_integral_of_laplaceMethod μ hc hγ hf hlim hmaj
  exact (hlim_int.eventually_ne hne).mono fun t ht hzero ↦ ht (by simp [hzero])

/-- **Laplace's method in several variables**: if `c, γ > 0`, `f t` is eventually `μ`-almost
everywhere strongly measurable, `f t ((Real.sqrt t)⁻¹ • v) → Complex.exp (-B v v)` for
`μ`-almost every `v : E`, and `‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))` holds eventually in `t`
for `μ`-almost every `v : E`, then `(B v v).re > 0` for all `v ≠ 0`, `f t` is eventually
`μ`-integrable, `t ^ (n / 2) * ∫ v, f t v ∂μ → ∫ v, Complex.exp (-B v v) ∂μ`, and eventually
`∫ v, f t v ∂μ ≠ 0`. -/
theorem laplaceMethod_multivariate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    {f : ℕ → E → ℂ} (hf : ∀ᶠ t in atTop, AEStronglyMeasurable (f t) μ)
    (hlim : ∀ᵐ v ∂μ,
      Tendsto (fun t : ℕ ↦ f t ((Real.sqrt t)⁻¹ • v)) atTop (𝓝 (Complex.exp (-B v v))))
    (hmaj : ∀ᶠ t in atTop, ∀ᵐ v ∂μ, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    (∀ v : E, v ≠ 0 → 0 < (B v v).re) ∧
      (∀ᶠ t in atTop, Integrable (f t) μ) ∧
      Tendsto (fun t : ℕ ↦ (((t : ℝ) ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ∫ v, f t v ∂μ)
        atTop (𝓝 (∫ v, Complex.exp (-B v v) ∂μ)) ∧
      ∀ᶠ t in atTop, ∫ v, f t v ∂μ ≠ 0 :=
  ⟨re_pos_of_laplaceMethod_of_ae μ B hc hγ hlim hmaj,
    eventually_integrable_of_laplaceMethod μ hc hγ hf hmaj,
    tendsto_rpow_mul_integral_of_laplaceMethod μ hc hγ hf hlim hmaj,
    eventually_integral_ne_zero_of_laplaceMethod μ B hc hγ hf hlim hmaj⟩

end TauCeti
