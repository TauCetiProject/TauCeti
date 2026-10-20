/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The inverse Gaussian distribution

The inverse Gaussian law with mean `m > 0` and shape `lam > 0` has density
`√(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - m) ^ 2) / (2 * m ^ 2 * x))` on the positive
half-line; the case `m = 1` is also called the Wald distribution. This file defines the law,
proves that it is a probability measure exactly when both parameters are positive, and computes
its cdf.

Invalid parameters give the zero density and hence the zero measure, so `inverseGaussianMeasure`
is a total family, measurable in its two parameters.

## Main definitions and results

* `inverseGaussianPDFReal`, `inverseGaussianPDF` and `inverseGaussianMeasure` define the density
  and the law; `integrable_inverseGaussianMeasure_iff` and `integral_inverseGaussianMeasure_eq`
  transfer integrability and integrals against the law to the density;
* `isProbabilityMeasure_inverseGaussianMeasure_iff` characterizes the valid parameter range;
* `hasPDF_of_hasLaw_inverseGaussianMeasure`,
  `pdf_eq_inverseGaussianPDF_of_hasLaw_inverseGaussianMeasure` and
  `rnDeriv_inverseGaussianMeasure` give the density interface;
* `support_inverseGaussianMeasure` identifies the topological support as `Ici 0`;
* `cdf_inverseGaussianMeasure_eq` gives the closed-form cdf
  `Φ (√(lam / x) * (x / m - 1)) + exp (2 * lam / m) * Φ (-(√(lam / x) * (x / m + 1)))` for
  `x > 0`, where `Φ` is the standard Gaussian cdf;
* `measurable_inverseGaussianMeasure` makes the family available for kernel constructions.

## Implementation

Normalization and the cdf come from one computation: the closed-form cdf is an antiderivative of
the density on the positive half-line, with limit `0` at `0⁺` and `1` at infinity. Differentiating
it produces two Gaussian density terms, and these combine because the squares of the two
Gaussian arguments differ by exactly `4 * lam / m`, which the factor `exp (2 * lam / m)`
compensates.

## References

* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter 15.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {m lam x : ℝ}

/-! ### Density and measure -/

/-- The real-valued inverse Gaussian density with mean `m` and shape `lam`:
`√(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - m) ^ 2) / (2 * m ^ 2 * x))` on the positive
half-line.

It is defined to be zero unless `m`, `lam`, and the sample point are all positive. -/
def inverseGaussianPDFReal (m lam x : ℝ) : ℝ :=
  if 0 < m ∧ 0 < lam ∧ 0 < x then
    √(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - m) ^ 2) / (2 * m ^ 2 * x))
  else 0

/-- The inverse Gaussian density, valued in `ℝ≥0∞`. -/
def inverseGaussianPDF (m lam x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseGaussianPDFReal m lam x)

/-- The inverse Gaussian law with mean `m` and shape `lam`.

For invalid parameters this is the zero measure; see `inverseGaussianMeasure_of_not_pos`. -/
def inverseGaussianMeasure (m lam : ℝ) : Measure ℝ :=
  volume.withDensity (inverseGaussianPDF m lam)

/-- An inverse Gaussian measure is Lebesgue measure weighted by its density. -/
theorem inverseGaussianMeasure_def (m lam : ℝ) :
    inverseGaussianMeasure m lam = volume.withDensity (inverseGaussianPDF m lam) := by
  rfl

/-- The `ℝ≥0∞`-valued density is the nonnegative coercion of the real density. -/
theorem inverseGaussianPDF_eq_ofReal (m lam x : ℝ) :
    inverseGaussianPDF m lam x = ENNReal.ofReal (inverseGaussianPDFReal m lam x) := by
  rw [inverseGaussianPDF]

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem inverseGaussianPDFReal_of_pos (hm : 0 < m) (hlam : 0 < lam) (hx : 0 < x) :
    inverseGaussianPDFReal m lam x =
      √(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - m) ^ 2) / (2 * m ^ 2 * x)) := by
  rw [inverseGaussianPDFReal, ite_eq_left ⟨hm, hlam, hx⟩]

/-- The density vanishes on the nonpositive half-line. -/
@[simp]
theorem inverseGaussianPDFReal_of_nonpos (hx : x ≤ 0) (m lam : ℝ) :
    inverseGaussianPDFReal m lam x = 0 := by
  rw [inverseGaussianPDFReal, ite_eq_right fun h => hx.not_gt h.2.2]

/-- The density vanishes outside the valid parameter range. -/
@[simp]
theorem inverseGaussianPDFReal_of_not_pos (h : ¬ (0 < m ∧ 0 < lam)) (x : ℝ) :
    inverseGaussianPDFReal m lam x = 0 := by
  rw [inverseGaussianPDFReal, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]

/-- The `ℝ≥0∞`-valued density vanishes on the nonpositive half-line. -/
@[simp]
theorem inverseGaussianPDF_of_nonpos (hx : x ≤ 0) (m lam : ℝ) :
    inverseGaussianPDF m lam x = 0 := by
  rw [inverseGaussianPDF_eq_ofReal, inverseGaussianPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes outside the valid parameter range. -/
@[simp]
theorem inverseGaussianPDF_of_not_pos (h : ¬ (0 < m ∧ 0 < lam)) (x : ℝ) :
    inverseGaussianPDF m lam x = 0 := by
  rw [inverseGaussianPDF_eq_ofReal, inverseGaussianPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- At valid parameters the density is strictly positive on the positive half-line. -/
theorem inverseGaussianPDFReal_pos (hm : 0 < m) (hlam : 0 < lam) (hx : 0 < x) :
    0 < inverseGaussianPDFReal m lam x := by
  rw [inverseGaussianPDFReal_of_pos hm hlam hx]
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) (exp_pos _)

/-- The real-valued inverse Gaussian density is nonnegative at every parameter. -/
theorem inverseGaussianPDFReal_nonneg (m lam x : ℝ) : 0 ≤ inverseGaussianPDFReal m lam x := by
  by_cases h : 0 < m ∧ 0 < lam ∧ 0 < x
  · exact (inverseGaussianPDFReal_pos h.1 h.2.1 h.2.2).le
  · rw [inverseGaussianPDFReal, ite_eq_right h]

/-- The two density representations agree under `ENNReal.toReal`. -/
@[simp]
theorem toReal_inverseGaussianPDF (m lam x : ℝ) :
    (inverseGaussianPDF m lam x).toReal = inverseGaussianPDFReal m lam x :=
  ENNReal.toReal_ofReal (inverseGaussianPDFReal_nonneg m lam x)

/-- The real inverse Gaussian density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGaussianPDFReal (m lam : ℝ) :
    Measurable (inverseGaussianPDFReal m lam) := by
  unfold inverseGaussianPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The `ℝ≥0∞`-valued inverse Gaussian density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGaussianPDF (m lam : ℝ) : Measurable (inverseGaussianPDF m lam) :=
  (measurable_inverseGaussianPDFReal m lam).ennreal_ofReal

/-- If either parameter is invalid, the inverse Gaussian measure is zero. -/
@[simp]
theorem inverseGaussianMeasure_of_not_pos (h : ¬ (0 < m ∧ 0 < lam)) :
    inverseGaussianMeasure m lam = 0 := by
  rw [inverseGaussianMeasure_def, funext (inverseGaussianPDF_of_not_pos h)]
  exact withDensity_zero

/-- An inverse Gaussian measure gives no mass to the nonpositive half-line. This also holds at
invalid parameters, where the measure is zero. -/
@[simp]
theorem inverseGaussianMeasure_Iic_zero (m lam : ℝ) :
    inverseGaussianMeasure m lam (Iic 0) = 0 := by
  rw [inverseGaussianMeasure_def, withDensity_apply _ measurableSet_Iic]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
  exact inverseGaussianPDF_of_nonpos hy m lam

/-- An inverse Gaussian random variable is almost surely positive, including vacuously at
invalid parameters. -/
theorem ae_pos_inverseGaussianMeasure (m lam : ℝ) :
    ∀ᵐ y ∂inverseGaussianMeasure m lam, 0 < y := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using inverseGaussianMeasure_Iic_zero m lam

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is integrable against an inverse Gaussian measure exactly when its
density-weighted version is Lebesgue integrable. This holds at every parameter. -/
theorem integrable_inverseGaussianMeasure_iff (m lam : ℝ) {g : ℝ → E} :
    Integrable g (inverseGaussianMeasure m lam) ↔
      Integrable (fun y ↦ inverseGaussianPDFReal m lam y • g y) := by
  rw [inverseGaussianMeasure_def, funext (inverseGaussianPDF_eq_ofReal m lam)]
  exact integrable_withDensity_ofReal_iff (measurable_inverseGaussianPDFReal m lam).aemeasurable
    (ae_of_all _ (inverseGaussianPDFReal_nonneg m lam))

/-- An integral against an inverse Gaussian measure is the density-weighted Lebesgue integral.
This holds at every parameter. -/
theorem integral_inverseGaussianMeasure_eq (m lam : ℝ) (g : ℝ → E) :
    ∫ y, g y ∂inverseGaussianMeasure m lam = ∫ y, inverseGaussianPDFReal m lam y • g y := by
  rw [inverseGaussianMeasure_def, funext (inverseGaussianPDF_eq_ofReal m lam)]
  exact integral_withDensity_ofReal (measurable_inverseGaussianPDFReal m lam).aemeasurable
    (ae_of_all _ (inverseGaussianPDFReal_nonneg m lam)) g

end Transfer

/-! ### The closed-form antiderivative -/

/-- The closed-form inverse Gaussian cdf on the positive half-line, in terms of the standard
Gaussian cdf. `cdf_inverseGaussianMeasure_eq` identifies it with the cdf. -/
private def cdfFormula (m lam x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (√(lam / x) * (x / m - 1)) +
    exp (2 * lam / m) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / m + 1)))

/-- On the positive half-line the closed form is an antiderivative of the density. -/
private lemma hasDerivAt_cdfFormula (hm : 0 < m) (hlam : 0 < lam) (hx : 0 < x) :
    HasDerivAt (cdfFormula m lam) (inverseGaussianPDFReal m lam x) x := by
  have hdiv : HasDerivAt (fun y => lam / y) (-(lam / x ^ 2)) x := by
    simpa [div_eq_mul_inv, mul_neg] using (hasDerivAt_inv hx.ne').const_mul lam
  have hsqrt := hdiv.sqrt (div_pos hlam hx).ne'
  have hA := hsqrt.mul (((hasDerivAt_id x).div_const m).sub_const 1)
  have hB := (hsqrt.mul (((hasDerivAt_id x).div_const m).add_const 1)).neg
  have hΦA := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp x hA
  have hΦB := ((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp x hB).const_mul
    (exp (2 * lam / m))
  refine (hΦA.add hΦB).congr_deriv ?_
  simp only [id_eq, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Pi.mul_apply,
    Pi.neg_apply, inverseGaussianPDFReal_of_pos hm hlam hx]
  set r := √(lam / x) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (div_pos hlam hx)
  have hrx : r ^ 2 * x = lam := by
    rw [hr, Real.sq_sqrt (div_pos hlam hx).le, div_mul_cancel₀ _ hx.ne']
  -- The squares of the two Gaussian arguments differ by `4 * lam / m`, so the factor
  -- `exp (2 * lam / m)` turns the second Gaussian density term into the first.
  have hexpB : exp (2 * lam / m) * exp (-(-(r * (x / m + 1))) ^ 2 / 2) =
      exp (-(r * (x / m - 1)) ^ 2 / 2) := by
    rw [← exp_add]
    congr 1
    linear_combination (-2 / m) * hrx
  have hexpA : exp (-(r * (x / m - 1)) ^ 2 / 2) =
      exp (-(lam * (x - m) ^ 2) / (2 * m ^ 2 * x)) := by
    congr 1
    rw [← hrx]
    field_simp
  have hcoef : √(lam / (2 * π * x ^ 3)) = (√(2 * π))⁻¹ * (r / x) := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), mul_pow, inv_pow,
      Real.sq_sqrt (by positivity), div_pow, ← hrx]
    field_simp
  calc _ = (√(2 * π))⁻¹ * exp (-(r * (x / m - 1)) ^ 2 / 2) *
        ((-(lam / x ^ 2) / (2 * r) * (x / m - 1) + r * (1 / m)) +
          -(-(lam / x ^ 2) / (2 * r) * (x / m + 1) + r * (1 / m))) := by
        rw [← hexpB]
        ring
    _ = _ := by
      rw [hexpA, hcoef, ← hrx]
      field_simp
      ring

/-- The closed form tends to `0` at `0⁺`, where both of its Gaussian arguments tend to `-∞`. -/
private lemma tendsto_cdfFormula_nhdsGT_zero (hlam : 0 < lam) :
    Tendsto (cdfFormula m lam) (𝓝[>] 0) (𝓝 0) := by
  have hsqrt : Tendsto (fun y : ℝ => √(lam / y)) (𝓝[>] 0) atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact (tendsto_inv_nhdsGT_zero.const_mul_atTop hlam).congr fun y =>
      (div_eq_mul_inv lam y).symm
  have hlin : ∀ c : ℝ, Tendsto (fun y : ℝ => y / m + c) (𝓝[>] 0) (𝓝 c) := fun c => by
    have : Continuous fun y : ℝ => y / m + c := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun y => √(lam / y) * (y / m - 1)) (𝓝[>] 0) atBot := by
    simpa only [sub_eq_add_neg] using hsqrt.atTop_mul_neg neg_one_lt_zero (hlin (-1))
  have hB : Tendsto (fun y => -(√(lam / y) * (y / m + 1))) (𝓝[>] 0) atBot :=
    tendsto_neg_atTop_atBot.comp (hsqrt.atTop_mul_pos one_pos (hlin 1))
  unfold cdfFormula
  simpa using ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp hA).add
    (((tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp hB).const_mul (exp (2 * lam / m)))

/-- The closed form tends to `1` at infinity, where its first Gaussian argument tends to `∞`
and its second to `-∞`. -/
private lemma tendsto_cdfFormula_atTop (hm : 0 < m) (hlam : 0 < lam) :
    Tendsto (cdfFormula m lam) atTop (𝓝 1) := by
  -- For `y > 0`, `√(lam / y) * (y / m + c)` is `√lam * (√y / m + c * (√y)⁻¹)`, which tends
  -- to infinity for every constant `c`.
  have heq : ∀ c : ℝ, (fun y => √lam * (√y / m + c * (√y)⁻¹)) =ᶠ[atTop]
      fun y => √(lam / y) * (y / m + c) := fun c => by
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hy' : 0 < √y := Real.sqrt_pos.2 hy
    rw [Real.sqrt_div hlam.le]
    field_simp
    rw [Real.sq_sqrt hy.le]
  have hsy : Tendsto (fun y : ℝ => √y) atTop atTop := Real.tendsto_sqrt_atTop
  have hlim : ∀ c : ℝ, Tendsto (fun y => √(lam / y) * (y / m + c)) atTop atTop := fun c =>
    (((hsy.atTop_div_const hm).atTop_add
      ((tendsto_inv_atTop_zero.comp hsy).const_mul c)).const_mul_atTop
        (Real.sqrt_pos.2 hlam)).congr' (heq c)
  have hA : Tendsto (fun y => √(lam / y) * (y / m - 1)) atTop atTop := by
    simpa only [sub_eq_add_neg] using hlim (-1)
  have hB : Tendsto (fun y => -(√(lam / y) * (y / m + 1))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (hlim 1)
  unfold cdfFormula
  simpa using ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).comp hA).add
    (((tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp hB).const_mul (exp (2 * lam / m)))

/-- The density is integrable on the positive half-line with integral one. -/
private lemma integrableOn_Ioi_zero_and_integral_eq (hm : 0 < m) (hlam : 0 < lam) :
    IntegrableOn (inverseGaussianPDFReal m lam) (Ioi 0) ∧
      ∫ y in Ioi 0, inverseGaussianPDFReal m lam y = 1 := by
  -- Extended by zero to the nonpositive half-line, the closed form is an antiderivative of the
  -- density that is continuous from the right at zero.
  set G : ℝ → ℝ := fun y => if y ≤ 0 then 0 else cdfFormula m lam y with hG
  have hG0 : G 0 = 0 := by simp [hG]
  have hGpos : ∀ y, 0 < y → G y = cdfFormula m lam y := fun y hy => by
    simp [hG, not_le.2 hy]
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
    exact (tendsto_cdfFormula_nhdsGT_zero hlam).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (hGpos y hy).symm)
  have hderiv : ∀ y ∈ Ioi 0, HasDerivAt G (inverseGaussianPDFReal m lam y) y := fun y hy =>
    (hasDerivAt_cdfFormula hm hlam hy).congr_of_eventuallyEq
      (eventually_of_mem (lt_mem_nhds hy) fun z hz => hGpos z hz)
  have hlim : Tendsto G atTop (𝓝 1) :=
    (tendsto_cdfFormula_atTop hm hlam).congr'
      (eventually_of_mem (Ioi_mem_atTop 0) fun y hy => (hGpos y hy).symm)
  have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ inverseGaussianPDFReal m lam y := fun y _ =>
    inverseGaussianPDFReal_nonneg m lam y
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn hlim, hG0, sub_zero]

/-! ### Normalization -/

/-- The real density is integrable at every parameter. -/
theorem integrable_inverseGaussianPDFReal (m lam : ℝ) :
    Integrable (inverseGaussianPDFReal m lam) := by
  by_cases h : 0 < m ∧ 0 < lam
  · refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).1
      (integrableOn_Ioi_zero_and_integral_eq h.1 h.2).1
    by_contra hy'
    exact hy (inverseGaussianPDFReal_of_nonpos (not_lt.1 hy') m lam)
  · simp [funext (inverseGaussianPDFReal_of_not_pos h)]

/-- The real inverse Gaussian density has total mass one at valid parameters. -/
theorem integral_inverseGaussianPDFReal (hm : 0 < m) (hlam : 0 < lam) :
    ∫ y, inverseGaussianPDFReal m lam y = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
    fun y hy => inverseGaussianPDFReal_of_nonpos (not_lt.1 hy) m lam]
  exact (integrableOn_Ioi_zero_and_integral_eq hm hlam).2

/-- The `ℝ≥0∞`-valued inverse Gaussian density has total mass one at valid parameters. -/
theorem lintegral_inverseGaussianPDF_eq_one (hm : 0 < m) (hlam : 0 < lam) :
    ∫⁻ y, inverseGaussianPDF m lam y = 1 := by
  simp_rw [inverseGaussianPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inverseGaussianPDFReal m lam)
      (ae_of_all _ (inverseGaussianPDFReal_nonneg m lam)),
    integral_inverseGaussianPDFReal hm hlam, ENNReal.ofReal_one]

/-- For positive mean and shape the inverse Gaussian law is a probability measure. -/
theorem isProbabilityMeasure_inverseGaussianMeasure (hm : 0 < m) (hlam : 0 < lam) :
    IsProbabilityMeasure (inverseGaussianMeasure m lam) := by
  constructor
  rw [inverseGaussianMeasure_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_inverseGaussianPDF_eq_one hm hlam]

/-- The inverse Gaussian law is a probability measure exactly for positive mean and shape. -/
@[simp]
theorem isProbabilityMeasure_inverseGaussianMeasure_iff :
    IsProbabilityMeasure (inverseGaussianMeasure m lam) ↔ 0 < m ∧ 0 < lam := by
  refine ⟨fun hp => ?_, fun h => isProbabilityMeasure_inverseGaussianMeasure h.1 h.2⟩
  by_contra h
  rw [inverseGaussianMeasure_of_not_pos h] at hp
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- Every inverse Gaussian measure is finite, including the zero measure at invalid
parameters. -/
instance : IsFiniteMeasure (inverseGaussianMeasure m lam) := by
  by_cases h : 0 < m ∧ 0 < lam
  · have := isProbabilityMeasure_inverseGaussianMeasure h.1 h.2
    infer_instance
  · rw [inverseGaussianMeasure_of_not_pos h]
    infer_instance

/-! ### Density interface and support -/

section DensityInterface

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with an inverse Gaussian law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_inverseGaussianMeasure (hX : HasLaw X (inverseGaussianMeasure m lam) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_inverseGaussianPDF m lam).aemeasurable hX

/-- The density of a random variable with an inverse Gaussian law is `inverseGaussianPDF`. -/
theorem pdf_eq_inverseGaussianPDF_of_hasLaw_inverseGaussianMeasure
    (hX : HasLaw X (inverseGaussianMeasure m lam) P) :
    pdf X P volume =ᵐ[volume] inverseGaussianPDF m lam :=
  pdf_eq_of_hasLaw_withDensity (measurable_inverseGaussianPDF m lam).aemeasurable hX

end DensityInterface

/-- The Radon–Nikodym derivative of an inverse Gaussian law is its density. -/
theorem rnDeriv_inverseGaussianMeasure (m lam : ℝ) :
    (inverseGaussianMeasure m lam).rnDeriv volume =ᵐ[volume] inverseGaussianPDF m lam :=
  Measure.rnDeriv_withDensity volume (measurable_inverseGaussianPDF m lam)

/-- The exact topological support is the closed positive half-line for valid parameters, and
empty otherwise. -/
@[simp]
theorem support_inverseGaussianMeasure (m lam : ℝ) :
    (inverseGaussianMeasure m lam).support = if 0 < m ∧ 0 < lam then Ici 0 else ∅ := by
  split_ifs with h
  · have hsupp : Function.support (inverseGaussianPDF m lam) = Ioi 0 := by
      ext y
      rw [Function.mem_support, mem_Ioi]
      refine ⟨fun hy => not_le.1 fun hy' => hy (inverseGaussianPDF_of_nonpos hy' m lam),
        fun hy => ?_⟩
      rw [inverseGaussianPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
      exact inverseGaussianPDFReal_pos h.1 h.2 hy
    rw [inverseGaussianMeasure_def,
      Measure.support_withDensity_eq_closure (measurable_inverseGaussianPDF m lam) isOpen_Ioi
        hsupp, closure_Ioi]
  · simp [inverseGaussianMeasure_of_not_pos h, Measure.support_zero]

/-! ### Cumulative distribution function -/

/-- Integrating the density computes the real mass of a measurable set. -/
private lemma measureReal_inverseGaussianMeasure {s : Set ℝ} (hs : MeasurableSet s) :
    (inverseGaussianMeasure m lam).real s = ∫ y in s, inverseGaussianPDFReal m lam y := by
  rw [inverseGaussianMeasure_def, funext (inverseGaussianPDF_eq_ofReal m lam)]
  exact measureReal_withDensity_ofReal (ae_of_all _ (inverseGaussianPDFReal_nonneg m lam)) hs
    (integrable_inverseGaussianPDFReal m lam).integrableOn

/-- The upper tail of a valid inverse Gaussian law is one minus the closed form. -/
private lemma measureReal_Ioi_inverseGaussianMeasure (hm : 0 < m) (hlam : 0 < lam) (hx : 0 < x) :
    (inverseGaussianMeasure m lam).real (Ioi x) = 1 - cdfFormula m lam x := by
  rw [measureReal_inverseGaussianMeasure measurableSet_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun y hy => hasDerivAt_cdfFormula hm hlam (hx.trans_le hy))
      (integrable_inverseGaussianPDFReal m lam).integrableOn (tendsto_cdfFormula_atTop hm hlam)]

/-- **The inverse Gaussian cdf.** It vanishes on the nonpositive half-line, and for `x > 0` it
is `Φ (√(lam / x) * (x / m - 1)) + exp (2 * lam / m) * Φ (-(√(lam / x) * (x / m + 1)))`, where
`Φ` is the standard Gaussian cdf. -/
theorem cdf_inverseGaussianMeasure_eq (hm : 0 < m) (hlam : 0 < lam) (x : ℝ) :
    cdf (inverseGaussianMeasure m lam) x =
      if x ≤ 0 then 0 else
        cdf (gaussianReal 0 1) (√(lam / x) * (x / m - 1)) +
          exp (2 * lam / m) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / m + 1))) := by
  have := isProbabilityMeasure_inverseGaussianMeasure hm hlam
  rw [cdf_eq_real]
  split_ifs with hx
  · rw [measureReal_def, measure_mono_null (Iic_subset_Iic.2 hx)
      (inverseGaussianMeasure_Iic_zero m lam), ENNReal.toReal_zero]
  · rw [← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ,
      measureReal_Ioi_inverseGaussianMeasure hm hlam (not_le.1 hx), sub_sub_cancel, cdfFormula]

/-! ### Parameter measurability -/

/-- The inverse Gaussian density is jointly measurable in mean, shape, and sample point. -/
@[fun_prop]
theorem measurable_uncurry_inverseGaussianPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ inverseGaussianPDF q.1.1 q.1.2 q.2 := by
  unfold inverseGaussianPDF inverseGaussianPDFReal
  exact (Measurable.ite (by measurability) (by fun_prop) measurable_const).ennreal_ofReal

/-- The inverse Gaussian family is measurable in its mean and shape. -/
@[fun_prop]
theorem measurable_inverseGaussianMeasure :
    Measurable fun p : ℝ × ℝ ↦ inverseGaussianMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_inverseGaussianPDF

end Probability

end TauCeti
