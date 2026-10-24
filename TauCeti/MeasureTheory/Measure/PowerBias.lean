/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.MeasureTheory.Measure.Weighted

/-!
# Power-biased probability laws

Power biasing reweights a positive real-valued law by a real power of its coordinate. The
normalization is inherited from `Measure.weighted`, so a zero or infinite power moment gives the
zero measure; for a law carried by `[0, ∞)` this happens whenever `x ^ q` is not integrable
(`powerBias_eq_zero_of_not_integrable`). This file establishes the basic normalization and
composition API.

This construction is useful for transporting moment formulas between members of a positive
distribution family. In particular, its composition law turns successive biases into addition
of their exponents.

For a law carried by `(0, ∞)` the weight `x ^ q` is `exp (q * log x)` almost everywhere, so power
biasing is the exponential tilting of `μ` by `q * log x` (`powerBias_eq_tilted`). A law with a
density `f` whose product with `x ^ q` is proportional to another probability density `g` has the
law with density `g` as its power bias (`powerBias_withDensity_ofReal`); this is the form in which
family identities are proved.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, Chapter 17.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace MeasureTheory.Measure

/-- The power bias of a real measure by exponent `q` is its normalized weighting by `x ^ q`.

The construction is the zero measure when the normalizing power moment is zero or infinite. -/
noncomputable def powerBias (μ : Measure ℝ) (q : ℝ) : Measure ℝ :=
  μ.weighted fun x => Real.toNNReal (x ^ q)

/-- The definition of a power-biased measure as a normalized weighted measure. -/
theorem powerBias_def (μ : Measure ℝ) (q : ℝ) :
    μ.powerBias q = μ.weighted fun x => Real.toNNReal (x ^ q) :=
  (rfl)

/-- The nonnegative weight defining power bias is measurable for every exponent. -/
theorem measurable_powerBiasWeight (q : ℝ) :
    Measurable fun x : ℝ => Real.toNNReal (x ^ q) := by
  apply Measurable.real_toNNReal
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (Real.continuousAt_rpow_const x q (.inl hx)).continuousWithinAt

/-- Biasing by exponent zero leaves a probability measure unchanged. -/
@[simp]
theorem powerBias_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : μ.powerBias 0 = μ := by
  rw [powerBias_def]
  have hweight : (fun x : ℝ => Real.toNNReal (x ^ (0 : ℝ))) = 1 := by
    funext x
    simp
  rw [hweight]
  exact Measure.weighted_one μ

/-- The normalizing constant of power bias is the extended-real form of the corresponding power
moment whenever that moment is integrable. -/
theorem lintegral_powerBiasWeight_eq_of_integrable {μ : Measure ℝ} {q : ℝ}
    (hμ : 0 ≤ᵐ[μ] id) (hq : Integrable (fun x : ℝ => x ^ q) μ) :
    ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (∫ x, x ^ q ∂μ) := by
  simp_rw [ENNReal.ofNNReal_toNNReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hq
    (hμ.mono fun x hx => Real.rpow_nonneg hx q)]

/-- A positive finite power moment makes the corresponding power bias a probability measure. -/
theorem isProbabilityMeasure_powerBias {μ : Measure ℝ} {q : ℝ}
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    IsProbabilityMeasure (μ.powerBias q) := by
  rw [powerBias_def]
  exact Measure.isProbabilityMeasure_weighted hpos hfin

/-- Under a valid first bias, a further real power is integrable exactly when the power with the
sum of the two exponents was integrable under the original law. -/
theorem integrable_rpow_powerBias_iff {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    Integrable (fun x : ℝ => x ^ r) (μ.powerBias q) ↔
      Integrable (fun x : ℝ => x ^ (q + r)) μ := by
  rw [powerBias_def, Measure.integrable_weighted_iff
    (measurable_powerBiasWeight q).aemeasurable hpos hfin]
  apply integrable_congr
  filter_upwards [hμ] with x hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.rpow_add hx, smul_eq_mul]

/-- The totalized power integral under a valid power bias is the ratio of two power integrals of
the original law. The preceding integrability criterion identifies when this is an expectation. -/
theorem integral_rpow_powerBias {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x : ℝ => x ^ q) μ) :
    ∫ x, x ^ r ∂μ.powerBias q =
      (∫ x, x ^ (q + r) ∂μ) / ∫ x, x ^ q ∂μ := by
  have hnonneg : 0 ≤ ∫ x, x ^ q ∂μ :=
    integral_nonneg_of_ae (hμ.mono fun x hx => Real.rpow_nonneg hx.le q)
  rw [powerBias_def, Measure.integral_weighted (measurable_powerBiasWeight q).aemeasurable,
    lintegral_powerBiasWeight_eq_of_integrable (hμ.mono fun x hx => hx.le) hq,
    ENNReal.toReal_ofReal hnonneg, smul_eq_mul]
  rw [inv_mul_eq_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.rpow_add hx, smul_eq_mul]

/-- After a valid first bias, applying another power bias adds the two exponents. -/
theorem powerBias_powerBias {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    (μ.powerBias q).powerBias r = μ.powerBias (q + r) := by
  simp only [powerBias_def]
  rw [Measure.weighted_weighted (measurable_powerBiasWeight q).aemeasurable hpos hfin]
  apply Measure.weighted_congr
  filter_upwards [hμ] with x hx
  apply NNReal.eq
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.coe_toNNReal _ (Real.rpow_nonneg hx.le r),
    Real.coe_toNNReal _ (Real.rpow_nonneg hx.le (q + r)), Real.rpow_add hx]

/-- Power biasing is the normalized reweighting by the extended-real density `x ^ q`. -/
theorem powerBias_eq_smul_withDensity (μ : Measure ℝ) (q : ℝ) :
    μ.powerBias q =
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ • μ.withDensity fun x => ENNReal.ofReal (x ^ q) := by
  simp_rw [powerBias_def, weighted_def, ENNReal.ofNNReal_toNNReal]

/-- The mass assigned by a power-biased measure to a measurable set. -/
theorem powerBias_apply (μ : Measure ℝ) (q : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ.powerBias q s =
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ * ∫⁻ x in s, ENNReal.ofReal (x ^ q) ∂μ := by
  rw [powerBias_eq_smul_withDensity, smul_apply, smul_eq_mul, withDensity_apply _ hs]

/-- The Radon-Nikodym derivative of a power-biased measure is its normalized power weight. -/
theorem rnDeriv_powerBias (μ : Measure ℝ) [SigmaFinite μ] (q : ℝ) :
    (μ.powerBias q).rnDeriv μ =ᵐ[μ] fun x =>
      (∫⁻ y, ENNReal.ofReal (y ^ q) ∂μ)⁻¹ * ENNReal.ofReal (x ^ q) :=
  rnDeriv_weighted μ (measurable_powerBiasWeight q).aemeasurable

/-- For a law carried by `[0, ∞)` under which `x ^ q` is not integrable, the normalizing power
moment is infinite, so the totalized power bias is the zero measure. -/
theorem powerBias_eq_zero_of_not_integrable {μ : Measure ℝ} {q : ℝ} (hμ : 0 ≤ᵐ[μ] id)
    (hq : ¬Integrable (fun x : ℝ => x ^ q) μ) : μ.powerBias q = 0 := by
  refine weighted_eq_zero_of_lintegral_eq_top ?_
  simp_rw [ENNReal.ofNNReal_toNNReal]
  by_contra h
  exact hq ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (hμ.mono fun x hx => Real.rpow_nonneg hx q)).2 (lt_top_iff_ne_top.2 h)⟩

/-- For a law carried by `(0, ∞)`, power biasing by `q` is exponential tilting by `q * log x`. -/
theorem powerBias_eq_tilted {μ : Measure ℝ} (hpos : ∀ᵐ x ∂μ, 0 < x) (q : ℝ) :
    μ.powerBias q = μ.tilted fun x => q * log x := by
  have hw : (fun x => ENNReal.ofReal (x ^ q)) =ᵐ[μ] fun x => ENNReal.ofReal (exp (q * log x)) :=
    (rpow_eventuallyEq_exp_mul_log hpos q).fun_comp ENNReal.ofReal
  rw [powerBias_eq_smul_withDensity, lintegral_congr_ae hw, withDensity_congr_ae hw]
  by_cases hint : Integrable (fun x => exp (q * log x)) μ
  · rcases eq_zero_or_neZero μ with rfl | _
    · simp
    have hI := integral_exp_pos hint
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (exp_pos _).le),
      ← ENNReal.ofReal_inv_of_pos hI, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
      Measure.tilted]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hI.le), div_eq_inv_mul]
  · have hZ : ∫⁻ x, ENNReal.ofReal (exp (q * log x)) ∂μ = ∞ := by
      by_contra h
      exact hint ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
        (ae_of_all _ fun _ => (exp_pos _).le)).2 (lt_top_iff_ne_top.2 h)⟩
    simp [hZ, tilted_of_not_integrable hint]

/-- A law carried by `(0, ∞)` under which `x ^ q` is integrable is absolutely continuous with
respect to its power-biased law, so the two are equivalent. -/
theorem absolutelyContinuous_powerBias {μ : Measure ℝ} {q : ℝ} (hpos : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x => x ^ q) μ) : μ ≪ μ.powerBias q := by
  rw [powerBias_eq_tilted hpos]
  exact absolutelyContinuous_tilted (hq.congr (rpow_eventuallyEq_exp_mul_log hpos q))

/-- **Power biasing a law with a density.** Let `ρ.withDensity f` be a law with a nonnegative
density `f`, and suppose `f x * x ^ q = c * g x` almost everywhere for a constant `c > 0` and a
function `g` such that `ρ.withDensity g` is a probability measure. Then the power-biased law is
`ρ.withDensity g`. -/
theorem powerBias_withDensity_ofReal {ρ : Measure ℝ} {f g : ℝ → ℝ} {q c : ℝ}
    [IsProbabilityMeasure (ρ.withDensity fun x => ENNReal.ofReal (g x))]
    (hf : AEMeasurable f ρ) (hf0 : 0 ≤ᵐ[ρ] f) (hc : 0 < c)
    (hfg : ∀ᵐ x ∂ρ, f x * x ^ q = c * g x) :
    (ρ.withDensity fun x => ENNReal.ofReal (f x)).powerBias q =
      ρ.withDensity fun x => ENNReal.ofReal (g x) := by
  rw [powerBias_def]
  refine weighted_eq_of_withDensity_eq_smul (c := ENNReal.ofReal c)
    (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top ?_
  simp_rw [ENNReal.ofNNReal_toNNReal]
  rw [← withDensity_mul₀ hf.ennreal_ofReal (by fun_prop),
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae ?_
  filter_upwards [hf0, hfg] with x hx0 hx
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hx0, hx,
    ENNReal.ofReal_mul hc.le]

end MeasureTheory.Measure
