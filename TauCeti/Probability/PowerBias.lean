/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.MeasureTheory.Measure.NormalizedWithDensity

/-!
# Power-biased laws

For a measure `μ` on `ℝ` and a real exponent `q`, the power-biased law `μ.powerBias q` reweights
`μ` by the density `x ↦ x ^ q` and normalizes the result:

  `μ.powerBias q = (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ • μ.withDensity (ENNReal.ofReal (· ^ q))`.

It is the normalized weighted law `MeasureTheory.Measure.normalizedWithDensity` for the weight
`ENNReal.ofReal (x ^ q)`, and its weight-independent facts are instances of that general API.

It is the law written `μ^⟨q⟩` in the literature; for `q = 1` and a nonnegative law it is the
size-biased law. The normalizing constant is taken in `ℝ≥0∞`, so the expression is totalized:
when `x ^ q` has infinite or zero integral the result is the zero measure. In particular
`μ.powerBias q` is always either zero or a probability measure.

For a law carried by `(0, ∞)` the weight `x ^ q` is `exp (q * log x)` almost everywhere, so power
biasing is the exponential tilting of `μ` by `q * log x` (`powerBias_eq_tilted`). Through this
identification the general tilting API of `Mathlib.MeasureTheory.Measure.Tilted` gives the
composition law and the moment transfer below.

## Main definitions

* `MeasureTheory.Measure.powerBias` — the power-biased law `μ^⟨q⟩`.

## Main results

* `MeasureTheory.Measure.powerBias_apply` and `MeasureTheory.Measure.rnDeriv_powerBias` — the
  masses of `μ^⟨q⟩` and its density `x ^ q / ∫ x ^ q` with respect to `μ`;
* `MeasureTheory.Measure.powerBias_eq_zero_iff` and
  `MeasureTheory.Measure.powerBias_of_not_integrable` — `μ^⟨q⟩` is zero exactly when `x ^ q` has
  zero or infinite integral, in particular when `μ` is carried by `(0, ∞)` and `x ^ q` is not
  integrable;
* `MeasureTheory.Measure.isZeroOrProbabilityMeasure_powerBias` and
  `MeasureTheory.Measure.isProbabilityMeasure_powerBias` — `μ^⟨q⟩` is always zero or a
  probability measure, and it is a probability measure when `μ` is nonzero, carried by `(0, ∞)`,
  and `x ^ q` is integrable;
* `MeasureTheory.Measure.powerBias_eq_tilted` — for a law carried by `(0, ∞)`, power biasing is
  exponential tilting by `q * log x`;
* `MeasureTheory.Measure.powerBias_zero` — biasing a probability measure by the exponent `0`
  returns it;
* `MeasureTheory.Measure.powerBias_powerBias` — composition adds the exponents;
* `MeasureTheory.Measure.integral_powerBias` and `MeasureTheory.Measure.lintegral_powerBias` —
  integration against `μ^⟨q⟩` is integration of `x ^ q • g x` against `μ`, normalized;
* `MeasureTheory.Measure.integrable_rpow_powerBias_iff` and
  `MeasureTheory.Measure.integral_rpow_powerBias` — `x ^ r` is integrable under `μ^⟨q⟩` exactly
  when `x ^ (q + r)` is integrable under `μ`, and then
  `E_{μ^⟨q⟩}[X ^ r] = E_μ[X ^ (q + r)] / E_μ[X ^ q]`;
* `MeasureTheory.Measure.powerBias_withDensity_ofReal` — the power-biased law of a law with a
  density `f` is the law whose density is proportional to `x ^ q * f x`, the form in which the
  family identities are proved.
-/

public section

noncomputable section

open Real Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {μ : Measure ℝ} {q : ℝ}

/-- The power-biased law `μ^⟨q⟩` of a measure `μ` on `ℝ`: `μ` reweighted by the density `x ^ q`
and normalized to total mass one. The normalization is taken in `ℝ≥0∞`, so the result is the zero
measure when `x ^ q` has zero or infinite integral against `μ`. -/
def powerBias (μ : Measure ℝ) (q : ℝ) : Measure ℝ :=
  μ.normalizedWithDensity fun x => ENNReal.ofReal (x ^ q)

/-- Power biasing is normalized weighting by `x ^ q`. -/
theorem powerBias_eq_normalizedWithDensity (μ : Measure ℝ) (q : ℝ) :
    μ.powerBias q = μ.normalizedWithDensity fun x => ENNReal.ofReal (x ^ q) := by
  rw [powerBias]

/-- Unfolding lemma for `MeasureTheory.Measure.powerBias`. -/
theorem powerBias_def (μ : Measure ℝ) (q : ℝ) :
    μ.powerBias q =
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ • μ.withDensity fun x => ENNReal.ofReal (x ^ q) := by
  rw [powerBias_eq_normalizedWithDensity, normalizedWithDensity_def]

/-- The power-biased law of the zero measure is zero. -/
@[simp]
theorem powerBias_zero_measure (q : ℝ) : (0 : Measure ℝ).powerBias q = 0 := by
  simp [powerBias_eq_normalizedWithDensity]

/-- At exponent `0` the weight is constant, so power biasing only normalizes. -/
@[simp]
theorem powerBias_zero' (μ : Measure ℝ) : μ.powerBias 0 = (μ univ)⁻¹ • μ := by
  simp [powerBias_def]

/-- Biasing a probability measure by the exponent `0` returns it. -/
theorem powerBias_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : μ.powerBias 0 = μ := by
  simp

/-- The mass of a measurable set under the power-biased law. -/
theorem powerBias_apply (μ : Measure ℝ) (q : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ.powerBias q s =
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ * ∫⁻ x in s, ENNReal.ofReal (x ^ q) ∂μ := by
  rw [powerBias_eq_normalizedWithDensity, normalizedWithDensity_apply _ _ hs]

/-- If `x ^ q` has zero integral, the power-biased law is zero. -/
theorem powerBias_of_lintegral_eq_zero (h : ∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ = 0) :
    μ.powerBias q = 0 :=
  normalizedWithDensity_of_lintegral_eq_zero h

/-- If `x ^ q` has infinite integral, the power-biased law is zero. -/
theorem powerBias_of_lintegral_eq_top (h : ∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ = ∞) :
    μ.powerBias q = 0 :=
  normalizedWithDensity_of_lintegral_eq_top h

/-- The power-biased law is zero exactly when `x ^ q` has zero or infinite integral. -/
theorem powerBias_eq_zero_iff :
    μ.powerBias q = 0 ↔
      ∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ = 0 ∨ ∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ = ∞ :=
  normalizedWithDensity_eq_zero_iff

/-- The Radon–Nikodym derivative of the power-biased law with respect to the original law is the
normalized weight `x ^ q`. -/
theorem rnDeriv_powerBias (μ : Measure ℝ) [SigmaFinite μ] (q : ℝ) :
    (μ.powerBias q).rnDeriv μ =ᵐ[μ]
      fun x => (∫⁻ y, ENNReal.ofReal (y ^ q) ∂μ)⁻¹ * ENNReal.ofReal (x ^ q) :=
  rnDeriv_normalizedWithDensity μ (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_ne_top)

/-- Integration of a nonnegative function against the power-biased law. -/
theorem lintegral_powerBias (μ : Measure ℝ) (q : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂μ.powerBias q =
      (∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ)⁻¹ * ∫⁻ x, ENNReal.ofReal (x ^ q) * g x ∂μ :=
  lintegral_normalizedWithDensity μ (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_ne_top) g

/-- A power-biased law is either zero or a probability measure. -/
instance isZeroOrProbabilityMeasure_powerBias (μ : Measure ℝ) (q : ℝ) :
    IsZeroOrProbabilityMeasure (μ.powerBias q) :=
  isZeroOrProbabilityMeasure_normalizedWithDensity _ _

/-- A power-biased law is absolutely continuous with respect to the original law. -/
theorem powerBias_absolutelyContinuous (μ : Measure ℝ) (q : ℝ) : μ.powerBias q ≪ μ :=
  normalizedWithDensity_absolutelyContinuous _ _

/-- For a law carried by `(0, ∞)`, power biasing by `q` is exponential tilting by `q * log x`. -/
theorem powerBias_eq_tilted (hpos : ∀ᵐ x ∂μ, 0 < x) (q : ℝ) :
    μ.powerBias q = μ.tilted fun x => q * log x := by
  have hw : (fun x => ENNReal.ofReal (x ^ q)) =ᵐ[μ] fun x => ENNReal.ofReal (exp (q * log x)) :=
    (rpow_eventuallyEq_exp_mul_log hpos q).fun_comp ENNReal.ofReal
  rw [powerBias_def, lintegral_congr_ae hw, withDensity_congr_ae hw]
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

/-- A nonzero law carried by `(0, ∞)` under which `x ^ q` is integrable has a power-biased law
that is a probability measure. -/
theorem isProbabilityMeasure_powerBias [NeZero μ] (hpos : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x => x ^ q) μ) : IsProbabilityMeasure (μ.powerBias q) := by
  rw [powerBias_eq_tilted hpos]
  exact isProbabilityMeasure_tilted (hq.congr (rpow_eventuallyEq_exp_mul_log hpos q))

/-- A law carried by `(0, ∞)` under which `x ^ q` is not integrable has zero power-biased law. -/
theorem powerBias_of_not_integrable (hpos : ∀ᵐ x ∂μ, 0 < x)
    (hq : ¬Integrable (fun x => x ^ q) μ) : μ.powerBias q = 0 := by
  rw [powerBias_eq_tilted hpos]
  exact tilted_of_not_integrable fun h => hq (h.congr (rpow_eventuallyEq_exp_mul_log hpos q).symm)

/-- A law carried by `(0, ∞)` under which `x ^ q` is integrable is absolutely continuous with
respect to its power-biased law, so the two are equivalent. -/
theorem absolutelyContinuous_powerBias (hpos : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x => x ^ q) μ) : μ ≪ μ.powerBias q := by
  rw [powerBias_eq_tilted hpos]
  exact absolutelyContinuous_tilted (hq.congr (rpow_eventuallyEq_exp_mul_log hpos q))

/-- Power biasing a law carried by `(0, ∞)` twice adds the exponents, as soon as the first
weight is integrable. -/
theorem powerBias_powerBias (hpos : ∀ᵐ x ∂μ, 0 < x) (hq : Integrable (fun x => x ^ q) μ)
    (r : ℝ) : (μ.powerBias q).powerBias r = μ.powerBias (q + r) := by
  have hpos' : ∀ᵐ x ∂μ.powerBias q, 0 < x := (powerBias_absolutelyContinuous μ q).ae_le hpos
  rw [powerBias_eq_tilted hpos', powerBias_eq_tilted hpos, powerBias_eq_tilted hpos,
    tilted_tilted (hq.congr (rpow_eventuallyEq_exp_mul_log hpos q))]
  congr 1
  funext x
  rw [Pi.add_apply, add_mul]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration against the power-biased law of a law carried by `(0, ∞)`: the integral of
`x ^ q • g x` against `μ`, divided by the normalizing constant `∫ x, x ^ q ∂μ`. -/
theorem integral_powerBias (hpos : ∀ᵐ x ∂μ, 0 < x) (q : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂μ.powerBias q = (∫ x, x ^ q ∂μ)⁻¹ • ∫ x, x ^ q • g x ∂μ := by
  have he := rpow_eventuallyEq_exp_mul_log hpos q
  rw [powerBias_eq_tilted hpos, integral_tilted, integral_congr_ae he, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [he] with x hx
  rw [hx, smul_smul, div_eq_inv_mul]

/-- A function is integrable against the power-biased law of a law carried by `(0, ∞)` exactly
when its product with `x ^ q` is integrable against the original law. -/
theorem integrable_powerBias_iff (hpos : ∀ᵐ x ∂μ, 0 < x) (hq : Integrable (fun x => x ^ q) μ)
    (g : ℝ → E) : Integrable g (μ.powerBias q) ↔ Integrable (fun x => x ^ q • g x) μ := by
  have he := rpow_eventuallyEq_exp_mul_log hpos q
  rw [powerBias_eq_tilted hpos, integrable_tilted_iff (hq.congr he)]
  refine integrable_congr ?_
  filter_upwards [he] with x hx
  rw [hx]

end Integral

/-- **Power-moment transfer, integrability.** If `x ^ q` is integrable under a law carried by
`(0, ∞)`, then `x ^ r` is integrable under its power-biased law exactly when `x ^ (q + r)` is
integrable under the original law. -/
theorem integrable_rpow_powerBias_iff (hpos : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x => x ^ q) μ) (r : ℝ) :
    Integrable (fun x => x ^ r) (μ.powerBias q) ↔ Integrable (fun x => x ^ (q + r)) μ := by
  rw [integrable_powerBias_iff hpos hq]
  refine integrable_congr ?_
  filter_upwards [hpos] with x hx
  rw [smul_eq_mul, rpow_add hx]

/-- **Power-moment transfer.** For a law carried by `(0, ∞)`,
`E_{μ^⟨q⟩}[X ^ r] = E_μ[X ^ (q + r)] / E_μ[X ^ q]`. Both sides are totalized: when `x ^ q` is not
integrable both vanish. -/
theorem integral_rpow_powerBias (hpos : ∀ᵐ x ∂μ, 0 < x) (q r : ℝ) :
    ∫ x, x ^ r ∂μ.powerBias q = (∫ x, x ^ (q + r) ∂μ) / ∫ x, x ^ q ∂μ := by
  rw [integral_powerBias hpos, smul_eq_mul, div_eq_inv_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hpos] with x hx
  rw [smul_eq_mul, rpow_add hx]

/-- If reweighting `μ` by `x ^ q` gives a positive finite multiple of a probability measure `ν`,
then `ν` is the power-biased law of `μ`. -/
theorem powerBias_eq_of_withDensity_eq_smul {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (h : (μ.withDensity fun x => ENNReal.ofReal (x ^ q)) = c • ν) : μ.powerBias q = ν :=
  normalizedWithDensity_eq_of_withDensity_eq_smul hc0 hc h

/-- **Power biasing a law with a density.** Let `ρ.withDensity f` be a law with a nonnegative
density `f`, and suppose `f x * x ^ q = c * g x` almost everywhere for a constant `c > 0` and a
function `g` such that `ρ.withDensity g` is a probability measure. Then the power-biased law is
`ρ.withDensity g`. -/
theorem powerBias_withDensity_ofReal {ρ : Measure ℝ} {f g : ℝ → ℝ} {c : ℝ}
    [IsProbabilityMeasure (ρ.withDensity fun x => ENNReal.ofReal (g x))]
    (hf : Measurable f) (hf0 : 0 ≤ᵐ[ρ] f) (hg : Measurable g) (hc : 0 < c)
    (hfg : ∀ᵐ x ∂ρ, f x * x ^ q = c * g x) :
    (ρ.withDensity fun x => ENNReal.ofReal (f x)).powerBias q =
      ρ.withDensity fun x => ENNReal.ofReal (g x) := by
  refine powerBias_eq_of_withDensity_eq_smul (c := ENNReal.ofReal c)
    (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top ?_
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop), ← withDensity_smul _ (by fun_prop)]
  refine withDensity_congr_ae ?_
  filter_upwards [hf0, hfg] with x hx0 hx
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hx0, hx,
    ENNReal.ofReal_mul hc.le]

end MeasureTheory.Measure
