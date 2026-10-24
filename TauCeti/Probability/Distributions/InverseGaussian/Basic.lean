/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Density
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Affine

/-!
# The inverse Gaussian distribution

For a mean `μ > 0` and a shape `lam > 0`, the inverse Gaussian law is the law on the
positive half-line with density

`√(lam / (2π x³)) * exp (-lam (x - μ)² / (2 μ² x))`.

It is the law of the time at which a Brownian motion with positive drift first reaches a fixed
positive level. This file defines it by its density, which vanishes at invalid parameters, and
develops the density API, normalization, support, cumulative distribution function, parameter
measurability, and positive scaling.

Normalization and the cumulative distribution function come from one explicit antiderivative of
the density on `(0, ∞)`, the classical closed form

`F(x) = Φ(√(lam / x) (x / μ - 1)) + exp (2 lam / μ) Φ(-√(lam / x) (x / μ + 1))`,

where `Φ` is the standard Gaussian cdf. It tends to `0` at `0⁺` and to `1` at infinity, so the
improper fundamental theorem of calculus gives total mass one and identifies `F` with the cdf.

The support argument for cdf strict increase is provided by
`MeasureTheory.Measure.strictMonoOn_cdf_of_subset_support`, generalized from the original proof of
`TauCeti.Probability.strictMonoOn_cdf_hyperexponentialMeasure`.

## Main definitions

* `TauCeti.Probability.inverseGaussianMeasure` — the inverse Gaussian law;
* `TauCeti.Probability.inverseGaussianPDFReal` and `TauCeti.Probability.inverseGaussianPDF` — its
  densities.

## Main results

* `TauCeti.Probability.integral_inverseGaussianPDFReal` and
  `TauCeti.Probability.isProbabilityMeasure_inverseGaussianMeasure_iff` — normalization, and
  probability exactly at positive parameters;
* `TauCeti.Probability.ae_pos_inverseGaussianMeasure` and
  `TauCeti.Probability.support_inverseGaussianMeasure` — the almost-sure carrier `(0, ∞)` and the
  topological support `[0, ∞)`;
* `TauCeti.Probability.hasPDF_of_hasLaw_inverseGaussianMeasure` and
  `TauCeti.Probability.rnDeriv_inverseGaussianMeasure` — the density interfaces;
* `TauCeti.Probability.cdf_inverseGaussianMeasure_of_pos` — the closed-form cdf;
* `TauCeti.Probability.strictMonoOn_cdf_inverseGaussianMeasure` — strict increase on `[0, ∞)`;
* `TauCeti.Probability.measurable_inverseGaussianMeasure` — joint measurability in the parameters;
* `TauCeti.Probability.inverseGaussianMeasure_map_const_mul` — multiplication by `b > 0` sends the
  parameters `(μ, lam)` to `(b μ, b lam)`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter 15.
* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {μ lam x : ℝ}

/-! ### Density -/

/-- The real-valued inverse Gaussian density with mean `μ` and shape `lam`, equal to
`√(lam / (2π x³)) * exp (-lam (x - μ)² / (2 μ² x))` on the positive half-line. It vanishes
for `x ≤ 0` and unless both parameters are positive. -/
def inverseGaussianPDFReal (μ lam x : ℝ) : ℝ :=
  if 0 < μ ∧ 0 < lam ∧ 0 < x then
    √(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x))
  else 0

/-- The inverse Gaussian density, valued in `ℝ≥0∞`. -/
def inverseGaussianPDF (μ lam x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseGaussianPDFReal μ lam x)

/-- The `ℝ≥0∞`-valued inverse Gaussian density is the coercion of the real-valued one. -/
theorem inverseGaussianPDF_eq_ofReal (μ lam x : ℝ) :
    inverseGaussianPDF μ lam x = ENNReal.ofReal (inverseGaussianPDFReal μ lam x) := (rfl)

/-- At positive parameters and a positive point, the real inverse Gaussian density has its
classical formula. -/
@[simp]
theorem inverseGaussianPDFReal_of_pos (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) :
    inverseGaussianPDFReal μ lam x =
      √(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x)) := by
  rw [inverseGaussianPDFReal, ite_eq_left ⟨hμ, hlam, hx⟩]

/-- The real inverse Gaussian density vanishes on the nonpositive half-line. -/
@[simp]
theorem inverseGaussianPDFReal_of_nonpos (hx : x ≤ 0) (μ lam : ℝ) :
    inverseGaussianPDFReal μ lam x = 0 :=
  ite_eq_right fun h ↦ (not_lt.mpr hx) h.2.2

/-- The real inverse Gaussian density vanishes unless both parameters are positive. -/
@[simp]
theorem inverseGaussianPDFReal_of_not_pos (h : ¬ (0 < μ ∧ 0 < lam)) (x : ℝ) :
    inverseGaussianPDFReal μ lam x = 0 :=
  ite_eq_right fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The real inverse Gaussian density is positive on the positive half-line at positive
parameters. -/
theorem inverseGaussianPDFReal_pos (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) :
    0 < inverseGaussianPDFReal μ lam x := by
  rw [inverseGaussianPDFReal_of_pos hμ hlam hx]
  exact mul_pos (sqrt_pos.mpr (by positivity)) (exp_pos _)

/-- The real inverse Gaussian density is nonnegative. -/
theorem inverseGaussianPDFReal_nonneg (μ lam x : ℝ) : 0 ≤ inverseGaussianPDFReal μ lam x := by
  unfold inverseGaussianPDFReal
  split_ifs
  · positivity
  · exact le_rfl

/-- Converting the inverse Gaussian density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_inverseGaussianPDF (μ lam x : ℝ) :
    (inverseGaussianPDF μ lam x).toReal = inverseGaussianPDFReal μ lam x :=
  ENNReal.toReal_ofReal (inverseGaussianPDFReal_nonneg μ lam x)

/-- At positive parameters and a positive point, the inverse Gaussian density has its classical
formula. -/
@[simp]
theorem inverseGaussianPDF_of_pos (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) :
    inverseGaussianPDF μ lam x = ENNReal.ofReal
      (√(lam / (2 * π * x ^ 3)) * exp (-(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x))) := by
  rw [inverseGaussianPDF_eq_ofReal, inverseGaussianPDFReal_of_pos hμ hlam hx]

/-- The inverse Gaussian density vanishes on the nonpositive half-line. -/
@[simp]
theorem inverseGaussianPDF_of_nonpos (hx : x ≤ 0) (μ lam : ℝ) :
    inverseGaussianPDF μ lam x = 0 := by
  rw [inverseGaussianPDF_eq_ofReal, inverseGaussianPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The inverse Gaussian density vanishes unless both parameters are positive. -/
@[simp]
theorem inverseGaussianPDF_of_not_pos (h : ¬ (0 < μ ∧ 0 < lam)) (x : ℝ) :
    inverseGaussianPDF μ lam x = 0 := by
  rw [inverseGaussianPDF_eq_ofReal, inverseGaussianPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The real inverse Gaussian density is jointly measurable in its parameters and the sample
point. -/
@[fun_prop]
theorem measurable_uncurry_inverseGaussianPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ inverseGaussianPDFReal q.1.1 q.1.2 q.2 := by
  unfold inverseGaussianPDFReal
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  have hzero : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ) := measurable_const
  exact (measurableSet_lt hzero measurable_fst.fst).inter
    ((measurableSet_lt hzero measurable_fst.snd).inter (measurableSet_lt hzero measurable_snd))

/-- The `ℝ≥0∞`-valued inverse Gaussian density is jointly measurable in its parameters and the
sample point. -/
@[fun_prop]
theorem measurable_uncurry_inverseGaussianPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ inverseGaussianPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_inverseGaussianPDFReal.ennreal_ofReal

/-- The real inverse Gaussian density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_inverseGaussianPDFReal (μ lam : ℝ) :
    Measurable (inverseGaussianPDFReal μ lam) :=
  measurable_uncurry_inverseGaussianPDFReal.comp (measurable_prodMk_left (x := (μ, lam)))

/-- The inverse Gaussian density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_inverseGaussianPDF (μ lam : ℝ) : Measurable (inverseGaussianPDF μ lam) :=
  (measurable_inverseGaussianPDFReal μ lam).ennreal_ofReal

/-! ### An antiderivative of the density -/

/-- For `y > 0`, the Gaussian argument `√(lam / y) * (y / μ + c)` of the cdf, rewritten in
terms of `√y`. -/
private theorem sqrt_div_mul_eq (lam μ c : ℝ) {y : ℝ} (hy : 0 < y) :
    √(lam / y) * (y / μ + c) = √lam * (√y / μ + c / √y) := by
  rw [sqrt_div' lam hy.le]
  field_simp
  rw [sq_sqrt hy.le]

/-- The derivative of `y ↦ √(lam / y) * (y / μ + c)` on the positive half-line. -/
private theorem hasDerivAt_sqrt_div_mul (hlam : 0 < lam) (μ c : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y ↦ √(lam / y) * (y / μ + c)) (√(lam / y) * (1 / μ - c / y) / 2) y := by
  have hpos : 0 < lam / y := div_pos hlam hy
  have hdiv : HasDerivAt (fun y ↦ lam / y) (-(lam / y ^ 2)) y := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hy.ne').const_mul lam
  have hsq := hdiv.sqrt hpos.ne'
  have hlin : HasDerivAt (fun y ↦ y / μ + c) (1 / μ) y := by
    simpa using ((hasDerivAt_id y).div_const μ).add_const c
  convert hsq.mul hlin using 1
  have hsq' : √(lam / y) ^ 2 = lam / y := sq_sqrt hpos.le
  field_simp
  rw [hsq']
  field_simp
  ring

/-- The closed-form inverse Gaussian cdf on the positive half-line. At `x ≤ 0` the expression is
meaningless; see `cdfFormulaExt`. -/
private def cdfFormula (μ lam x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (√(lam / x) * (x / μ - 1)) +
    exp (2 * lam / μ) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / μ + 1)))

/-- On the positive half-line, the closed-form cdf has the density as its derivative. The two
Gaussian arguments `w₁ = √(lam / x) (x / μ - 1)` and `w₂ = √(lam / x) (x / μ + 1)` satisfy
`w₂ ^ 2 - w₁ ^ 2 = 4 lam / μ`, so the factor `exp (2 lam / μ)` turns `φ(w₂)` into `φ(w₁)` and the
two chain-rule terms combine. -/
private theorem hasDerivAt_cdfFormula (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) :
    HasDerivAt (cdfFormula μ lam) (inverseGaussianPDFReal μ lam x) x := by
  set r := √(lam / x) with hr_def
  have hr2 : r ^ 2 = lam / x := sq_sqrt (div_pos hlam hx).le
  have h1 := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp x
    (hasDerivAt_sqrt_div_mul hlam μ (-1) hx)
  have h2 := ((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp x
    (hasDerivAt_sqrt_div_mul hlam μ 1 hx).neg).const_mul (exp (2 * lam / μ))
  convert h1.add h2 using 1
  · funext y
    simp [cdfFormula, sub_eq_add_neg]
  set A := exp (-(r * (x / μ + -1)) ^ 2 / 2) with hA
  have hφ1 : gaussianPDFReal 0 1 (r * (x / μ + -1)) = (√(2 * π))⁻¹ * A := by
    simp [gaussianPDFReal, hA]
  have hφ2 : exp (2 * lam / μ) * gaussianPDFReal 0 1 (-(r * (x / μ + 1))) =
      (√(2 * π))⁻¹ * A := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, hA]
    rw [mul_left_comm, ← exp_add]
    congr 2
    rw [neg_sq, mul_pow, mul_pow, hr2]
    field_simp
    ring
  -- Write the radicand as a quotient by a perfect square, so that the square root splits.
  have hrad : lam / (2 * π * x ^ 3) = (lam / x) / (√(2 * π) * x) ^ 2 := by
    rw [mul_pow, sq_sqrt (by positivity)]
    field_simp
  have hS : √(lam / (2 * π * x ^ 3)) = r / (√(2 * π) * x) := by
    rw [hrad, sqrt_div' _ (sq_nonneg _), sqrt_sq (by positivity)]
  have hE : -(lam * (x - μ) ^ 2) / (2 * μ ^ 2 * x) = -(r * (x / μ + -1)) ^ 2 / 2 := by
    rw [mul_pow, hr2]
    field_simp
    ring
  rw [inverseGaussianPDFReal_of_pos hμ hlam hx, Pi.neg_apply, ← hr_def, hφ1,
    ← mul_assoc (exp _), hφ2, hS, hE, ← hA]
  field_simp
  ring

/-- The closed-form cdf tends to `0` at `0` from the right: both Gaussian arguments tend to
`-∞`. -/
private theorem tendsto_cdfFormula_nhdsGT_zero (hlam : 0 < lam) (μ : ℝ) :
    Tendsto (cdfFormula μ lam) (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun y ↦ √(lam / y)) (𝓝[>] 0) atTop :=
    tendsto_sqrt_atTop.comp ((tendsto_inv_nhdsGT_zero.const_mul_atTop hlam).congr
      fun y ↦ (div_eq_mul_inv lam y).symm)
  have hlin (c : ℝ) : Tendsto (fun y ↦ y / μ + c) (𝓝[>] 0) (𝓝 c) := by
    have h : Tendsto (fun y : ℝ ↦ y / μ + c) (𝓝 0) (𝓝 (0 / μ + c)) :=
      ((continuous_id.div_const μ).add continuous_const).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hw₁ : Tendsto (fun y ↦ √(lam / y) * (y / μ - 1)) (𝓝[>] 0) atBot := by
    simpa only [sub_eq_add_neg] using hr.atTop_mul_neg (neg_one_lt_zero) (hlin (-1))
  have hw₂ : Tendsto (fun y ↦ -(√(lam / y) * (y / μ + 1))) (𝓝[>] 0) atBot :=
    tendsto_neg_atTop_atBot.comp (hr.atTop_mul_pos one_pos (hlin 1))
  have h := ((tendsto_cdf_atBot (gaussianReal 0 1)).comp hw₁).add
    (((tendsto_cdf_atBot (gaussianReal 0 1)).comp hw₂).const_mul (exp (2 * lam / μ)))
  rw [mul_zero, add_zero] at h
  exact h

/-- The closed-form cdf tends to `1` at infinity. -/
private theorem tendsto_cdfFormula_atTop (hμ : 0 < μ) (hlam : 0 < lam) :
    Tendsto (cdfFormula μ lam) atTop (𝓝 1) := by
  have hs : Tendsto (fun y ↦ √y) atTop atTop := tendsto_sqrt_atTop
  have hw₁ : Tendsto (fun y ↦ √(lam / y) * (y / μ - 1)) atTop atTop := by
    have h : Tendsto (fun y ↦ √lam * (√y / μ + -1 / √y)) atTop atTop :=
      ((hs.atTop_div_const hμ).atTop_add (tendsto_const_nhds.div_atTop hs)).const_mul_atTop
        (sqrt_pos.mpr hlam)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [sub_eq_add_neg, sqrt_div_mul_eq lam μ (-1) hy]
  have hw₂ : Tendsto (fun y ↦ -(√(lam / y) * (y / μ + 1))) atTop atBot := by
    refine tendsto_neg_atTop_atBot.comp (tendsto_atTop_mono (fun y ↦ ?_) hw₁)
    nlinarith [sqrt_nonneg (lam / y)]
  have h := ((tendsto_cdf_atTop (gaussianReal 0 1)).comp hw₁).add
    (((tendsto_cdf_atBot (gaussianReal 0 1)).comp hw₂).const_mul (exp (2 * lam / μ)))
  rw [mul_zero, add_zero] at h
  exact h

/-- The density restricted to a half-line `(a, ∞)` inside the positive half-line integrates to
one minus the closed-form cdf at `a`. -/
private theorem integral_Ioi_inverseGaussianPDFReal_of_pos (hμ : 0 < μ) (hlam : 0 < lam)
    {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, inverseGaussianPDFReal μ lam x = 1 - cdfFormula μ lam a :=
  integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun _ hx ↦ hasDerivAt_cdfFormula hμ hlam (ha.trans_le hx))
    (fun x _ ↦ inverseGaussianPDFReal_nonneg μ lam x) (tendsto_cdfFormula_atTop hμ hlam)

/-- The closed-form cdf extended by zero to the nonpositive half-line, an antiderivative of the
density on `(0, ∞)` that is right-continuous at `0`. -/
private def cdfFormulaExt (μ lam : ℝ) : ℝ → ℝ := (Ioi 0).indicator (cdfFormula μ lam)

private theorem cdfFormulaExt_zero (μ lam : ℝ) : cdfFormulaExt μ lam 0 = 0 :=
  indicator_of_notMem (by simp) _

private theorem continuousWithinAt_cdfFormulaExt (hlam : 0 < lam) (μ : ℝ) :
    ContinuousWithinAt (cdfFormulaExt μ lam) (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, cdfFormulaExt_zero]
  exact (tendsto_cdfFormula_nhdsGT_zero hlam μ).congr'
    (eventuallyEq_nhdsWithin_of_eqOn eqOn_indicator).symm

private theorem hasDerivAt_cdfFormulaExt (hμ : 0 < μ) (hlam : 0 < lam) (hx : x ∈ Ioi 0) :
    HasDerivAt (cdfFormulaExt μ lam) (inverseGaussianPDFReal μ lam x) x :=
  (hasDerivAt_cdfFormula hμ hlam hx).congr_of_eventuallyEq
    (eventuallyEq_of_mem (Ioi_mem_nhds hx) eqOn_indicator)

private theorem tendsto_cdfFormulaExt_atTop (hμ : 0 < μ) (hlam : 0 < lam) :
    Tendsto (cdfFormulaExt μ lam) atTop (𝓝 1) :=
  (tendsto_cdfFormula_atTop hμ hlam).congr'
    (eventuallyEq_of_mem (Ioi_mem_atTop 0) eqOn_indicator).symm

private theorem integrableOn_Ioi_zero_inverseGaussianPDFReal (hμ : 0 < μ) (hlam : 0 < lam) :
    IntegrableOn (inverseGaussianPDFReal μ lam) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_cdfFormulaExt hlam μ)
    (fun _ ↦ hasDerivAt_cdfFormulaExt hμ hlam)
    (fun x _ ↦ inverseGaussianPDFReal_nonneg μ lam x) (tendsto_cdfFormulaExt_atTop hμ hlam)

private theorem integral_Ioi_zero_inverseGaussianPDFReal (hμ : 0 < μ) (hlam : 0 < lam) :
    ∫ x in Ioi 0, inverseGaussianPDFReal μ lam x = 1 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_cdfFormulaExt hlam μ)
    (fun _ ↦ hasDerivAt_cdfFormulaExt hμ hlam)
    (fun x _ ↦ inverseGaussianPDFReal_nonneg μ lam x) (tendsto_cdfFormulaExt_atTop hμ hlam),
    cdfFormulaExt_zero, sub_zero]

/-- The real inverse Gaussian density is Lebesgue integrable. -/
theorem integrable_inverseGaussianPDFReal (μ lam : ℝ) :
    Integrable (inverseGaussianPDFReal μ lam) := by
  by_cases h : 0 < μ ∧ 0 < lam
  · rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ (integrableOn_Ioi_zero_inverseGaussianPDFReal h.1 h.2)
    exact integrableOn_zero.congr_fun
      (fun x hx ↦ (inverseGaussianPDFReal_of_nonpos hx μ lam).symm) measurableSet_Iic
  · rw [funext (inverseGaussianPDFReal_of_not_pos h)]
    exact integrable_zero _ _ _

/-- **Normalization of the inverse Gaussian density.** At positive parameters the real density
integrates to one. -/
theorem integral_inverseGaussianPDFReal (hμ : 0 < μ) (hlam : 0 < lam) :
    ∫ x, inverseGaussianPDFReal μ lam x = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
    fun x hx ↦ inverseGaussianPDFReal_of_nonpos (not_lt.mp hx) μ lam]
  exact integral_Ioi_zero_inverseGaussianPDFReal hμ hlam

/-- At positive parameters the inverse Gaussian density has total mass one. -/
theorem lintegral_inverseGaussianPDF (hμ : 0 < μ) (hlam : 0 < lam) :
    ∫⁻ x, inverseGaussianPDF μ lam x = 1 := by
  simp_rw [inverseGaussianPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_inverseGaussianPDFReal μ lam)
    (ae_of_all _ (inverseGaussianPDFReal_nonneg μ lam)), integral_inverseGaussianPDFReal hμ hlam,
    ENNReal.ofReal_one]

/-! ### The law -/

/-- The inverse Gaussian law with mean `μ` and shape `lam`: Lebesgue measure weighted by
`inverseGaussianPDF μ lam`. It is the zero measure unless both parameters are positive. -/
def inverseGaussianMeasure (μ lam : ℝ) : Measure ℝ :=
  volume.withDensity (inverseGaussianPDF μ lam)

/-- The inverse Gaussian law is Lebesgue measure weighted by its density. -/
theorem inverseGaussianMeasure_eq_withDensity (μ lam : ℝ) :
    inverseGaussianMeasure μ lam = volume.withDensity (inverseGaussianPDF μ lam) := (rfl)

/-- Inverse Gaussian measures have no atoms, including at invalid parameters. -/
instance (μ lam : ℝ) : NullSingletonClass (inverseGaussianMeasure μ lam) := by
  rw [inverseGaussianMeasure_eq_withDensity]
  infer_instance

/-- At invalid parameters the inverse Gaussian law is the zero measure. -/
@[simp]
theorem inverseGaussianMeasure_of_not_pos (h : ¬ (0 < μ ∧ 0 < lam)) :
    inverseGaussianMeasure μ lam = 0 := by
  have hpdf : inverseGaussianPDF μ lam = 0 := funext (inverseGaussianPDF_of_not_pos h)
  rw [inverseGaussianMeasure_eq_withDensity, hpdf, withDensity_zero]

/-- An inverse Gaussian law with positive parameters is a probability measure. -/
theorem isProbabilityMeasure_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    IsProbabilityMeasure (inverseGaussianMeasure μ lam) :=
  ⟨by rw [inverseGaussianMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_inverseGaussianPDF hμ hlam]⟩

/-- The inverse Gaussian law is a probability measure exactly at positive parameters. -/
@[simp]
theorem isProbabilityMeasure_inverseGaussianMeasure_iff :
    IsProbabilityMeasure (inverseGaussianMeasure μ lam) ↔ 0 < μ ∧ 0 < lam := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_inverseGaussianMeasure h.1 h.2⟩
  by_contra hp
  rw [inverseGaussianMeasure_of_not_pos hp] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- Every inverse Gaussian measure is finite, including the zero measure at invalid
parameters. -/
instance : IsFiniteMeasure (inverseGaussianMeasure μ lam) := by
  by_cases h : 0 < μ ∧ 0 < lam
  · have := isProbabilityMeasure_inverseGaussianMeasure h.1 h.2
    infer_instance
  · rw [inverseGaussianMeasure_of_not_pos h]
    infer_instance

/-- The inverse Gaussian law gives no mass to the nonpositive half-line, at all parameters. -/
@[simp]
theorem inverseGaussianMeasure_Iic_zero (μ lam : ℝ) :
    inverseGaussianMeasure μ lam (Iic 0) = 0 := by
  rw [inverseGaussianMeasure_eq_withDensity, withDensity_apply _ measurableSet_Iic,
    setLIntegral_congr_fun measurableSet_Iic fun x hx ↦ inverseGaussianPDF_of_nonpos hx μ lam,
    lintegral_zero]

/-- An inverse Gaussian variable is almost surely positive, at all parameters. -/
theorem ae_pos_inverseGaussianMeasure (μ lam : ℝ) :
    ∀ᵐ x ∂inverseGaussianMeasure μ lam, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using inverseGaussianMeasure_Iic_zero μ lam

/-- At positive parameters, the topological support of the inverse Gaussian law is the closed
half-line `[0, ∞)`. -/
theorem support_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    (inverseGaussianMeasure μ lam).support = Ici 0 := by
  have hsupp : Function.support (inverseGaussianPDF μ lam) = Ioi 0 := by
    ext x
    rw [Function.mem_support, mem_Ioi]
    refine ⟨fun hx ↦ not_le.mp fun h ↦ hx (inverseGaussianPDF_of_nonpos h μ lam),
      fun hx ↦ ?_⟩
    rw [inverseGaussianPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
    exact inverseGaussianPDFReal_pos hμ hlam hx
  rw [inverseGaussianMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_inverseGaussianPDF μ lam) isOpen_Ioi hsupp,
    closure_Ioi]

/-- The exact topological support is the closed positive half-line at valid parameters and is
empty otherwise. -/
@[simp]
theorem support_inverseGaussianMeasure_eq_if (μ lam : ℝ) :
    (inverseGaussianMeasure μ lam).support = if 0 < μ ∧ 0 < lam then Ici 0 else ∅ := by
  by_cases h : 0 < μ ∧ 0 < lam
  · rw [ite_eq_left h, support_inverseGaussianMeasure h.1 h.2]
  · rw [ite_eq_right h, inverseGaussianMeasure_of_not_pos h, Measure.support_zero]

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against an inverse Gaussian law exactly
when its density-weighted version is Lebesgue integrable, at every parameter. -/
theorem integrable_inverseGaussianMeasure_iff (μ lam : ℝ) {g : ℝ → E} :
    Integrable g (inverseGaussianMeasure μ lam) ↔
      Integrable (fun x ↦ inverseGaussianPDFReal μ lam x • g x) := by
  rw [inverseGaussianMeasure_eq_withDensity, funext (inverseGaussianPDF_eq_ofReal μ lam)]
  exact integrable_withDensity_ofReal_iff (measurable_inverseGaussianPDFReal μ lam).aemeasurable
    (ae_of_all _ (inverseGaussianPDFReal_nonneg μ lam))

/-- **Integral transfer.** An integral against an inverse Gaussian law is the density-weighted
Lebesgue integral, at every parameter. -/
theorem integral_inverseGaussianMeasure_eq (μ lam : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂inverseGaussianMeasure μ lam = ∫ x, inverseGaussianPDFReal μ lam x • g x := by
  rw [inverseGaussianMeasure_eq_withDensity, funext (inverseGaussianPDF_eq_ofReal μ lam)]
  exact integral_withDensity_ofReal (measurable_inverseGaussianPDFReal μ lam).aemeasurable
    (ae_of_all _ (inverseGaussianPDFReal_nonneg μ lam)) g

end Transfer

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with an inverse Gaussian law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_inverseGaussianMeasure
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_inverseGaussianPDF μ lam).aemeasurable hX

/-- The density of a random variable with an inverse Gaussian law is `inverseGaussianPDF`. -/
theorem pdf_eq_inverseGaussianPDF_of_hasLaw_inverseGaussianMeasure
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) :
    pdf X P volume =ᵐ[volume] inverseGaussianPDF μ lam :=
  pdf_eq_of_hasLaw_withDensity (measurable_inverseGaussianPDF μ lam).aemeasurable hX

end RandomVariables

/-- The Radon–Nikodym derivative of an inverse Gaussian law with respect to Lebesgue measure. -/
theorem rnDeriv_inverseGaussianMeasure (μ lam : ℝ) :
    (inverseGaussianMeasure μ lam).rnDeriv volume =ᵐ[volume] inverseGaussianPDF μ lam :=
  Measure.rnDeriv_withDensity volume (measurable_inverseGaussianPDF μ lam)

/-- The totalized inverse Gaussian family is jointly measurable in its mean and shape. -/
@[fun_prop]
theorem measurable_inverseGaussianMeasure :
    Measurable fun p : ℝ × ℝ ↦ inverseGaussianMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_inverseGaussianPDF

/-! ### Cumulative distribution function -/

/-- **The inverse Gaussian cdf.** At positive parameters and a positive point,
`F(x) = Φ(√(lam / x) (x / μ - 1)) + exp (2 lam / μ) Φ(-√(lam / x) (x / μ + 1))`, where `Φ` is
the standard Gaussian cdf. -/
theorem cdf_inverseGaussianMeasure_of_pos (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) :
    cdf (inverseGaussianMeasure μ lam) x =
      cdf (gaussianReal 0 1) (√(lam / x) * (x / μ - 1)) +
        exp (2 * lam / μ) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / μ + 1))) := by
  have := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  have hint : IntegrableOn (inverseGaussianPDFReal μ lam) (Ioi x) :=
    (integrable_inverseGaussianPDFReal μ lam).integrableOn
  rw [cdf_eq_real, ← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ,
    inverseGaussianMeasure_eq_withDensity, funext (inverseGaussianPDF_eq_ofReal μ lam),
    measureReal_withDensity_ofReal (ae_of_all _ (inverseGaussianPDFReal_nonneg μ lam))
      measurableSet_Ioi hint,
    integral_Ioi_inverseGaussianPDFReal_of_pos hμ hlam hx, sub_sub_cancel, cdfFormula]

/-- The inverse Gaussian cdf vanishes on the nonpositive half-line. -/
theorem cdf_inverseGaussianMeasure_of_nonpos (hμ : 0 < μ) (hlam : 0 < lam) (hx : x ≤ 0) :
    cdf (inverseGaussianMeasure μ lam) x = 0 := by
  have := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  rw [cdf_eq_real, measureReal_def,
    measure_mono_null (Iic_subset_Iic.mpr hx) (inverseGaussianMeasure_Iic_zero μ lam),
    ENNReal.toReal_zero]

/-- **The inverse Gaussian cdf.** It vanishes on the nonpositive half-line and has the classical
closed form on the positive half-line. -/
theorem cdf_inverseGaussianMeasure_eq (hμ : 0 < μ) (hlam : 0 < lam) (x : ℝ) :
    cdf (inverseGaussianMeasure μ lam) x =
      if x ≤ 0 then 0 else
        cdf (gaussianReal 0 1) (√(lam / x) * (x / μ - 1)) +
          exp (2 * lam / μ) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / μ + 1))) := by
  split_ifs with hx
  · exact cdf_inverseGaussianMeasure_of_nonpos hμ hlam hx
  · exact cdf_inverseGaussianMeasure_of_pos hμ hlam (not_le.mp hx)

/-- The inverse Gaussian cdf is strictly increasing on the nonnegative half-line. -/
theorem strictMonoOn_cdf_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    StrictMonoOn (cdf (inverseGaussianMeasure μ lam)) (Ici 0) := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (by rw [support_inverseGaussianMeasure hμ hlam])

/-- The inverse Gaussian cdf is positive exactly at positive cutoffs. -/
@[simp]
theorem cdf_inverseGaussianMeasure_pos_iff (hμ : 0 < μ) (hlam : 0 < lam) :
    0 < cdf (inverseGaussianMeasure μ lam) x ↔ 0 < x := by
  constructor
  · intro hx
    by_contra h
    rw [cdf_inverseGaussianMeasure_of_nonpos hμ hlam (not_lt.mp h)] at hx
    exact lt_irrefl _ hx
  · intro hx
    exact (cdf_nonneg _ 0).trans_lt
      (strictMonoOn_cdf_inverseGaussianMeasure hμ hlam (by simp) hx.le hx)

/-- Every finite cutoff leaves positive inverse Gaussian upper-tail probability. -/
theorem cdf_inverseGaussianMeasure_lt_one (hμ : 0 < μ) (hlam : 0 < lam) (x : ℝ) :
    cdf (inverseGaussianMeasure μ lam) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_inverseGaussianMeasure hμ hlam) x

/-! ### Positive scaling -/

/-- The inverse Gaussian density satisfies the scaling identity: for `b > 0`, the density with
parameters `(b μ, b lam)` at `x` is `b⁻¹` times the density with parameters `(μ, lam)` at
`x / b`. -/
theorem inverseGaussianPDFReal_mul_mul {b : ℝ} (hb : 0 < b) (μ lam x : ℝ) :
    inverseGaussianPDFReal (b * μ) (b * lam) x =
      b⁻¹ * inverseGaussianPDFReal μ lam (x / b) := by
  by_cases h : 0 < μ ∧ 0 < lam ∧ 0 < x
  · obtain ⟨hμ, hlam, hx⟩ := h
    rw [inverseGaussianPDFReal_of_pos (mul_pos hb hμ) (mul_pos hb hlam) hx,
      inverseGaussianPDFReal_of_pos hμ hlam (div_pos hx hb)]
    have hsq : lam / (2 * π * (x / b) ^ 3) = b ^ 2 * (b * lam / (2 * π * x ^ 3)) := by
      field_simp
    rw [hsq, sqrt_mul (sq_nonneg b), sqrt_sq hb.le]
    have hexp : -(b * lam * (x - b * μ) ^ 2) / (2 * (b * μ) ^ 2 * x) =
        -(lam * (x / b - μ) ^ 2) / (2 * μ ^ 2 * (x / b)) := by
      field_simp
    rw [hexp]
    field_simp
  · have h' : ¬ (0 < b * μ ∧ 0 < b * lam ∧ 0 < x) := by
      rwa [mul_pos_iff_of_pos_left hb, mul_pos_iff_of_pos_left hb]
    have h'' : ¬ (0 < μ ∧ 0 < lam ∧ 0 < x / b) := by rwa [div_pos_iff_of_pos_right hb]
    rw [inverseGaussianPDFReal, ite_eq_right h', inverseGaussianPDFReal, ite_eq_right h'',
      mul_zero]

/-- **Positive scaling.** For `b > 0`, the law of `b X` for an inverse Gaussian variable `X` with
parameters `(μ, lam)` is the inverse Gaussian law with parameters `(b μ, b lam)`. The identity
also holds on the invalid zero branch. -/
theorem inverseGaussianMeasure_map_const_mul {b : ℝ} (hb : 0 < b) (μ lam : ℝ) :
    (inverseGaussianMeasure μ lam).map (fun x ↦ b * x) =
      inverseGaussianMeasure (b * μ) (b * lam) := by
  have hfun : (fun x : ℝ ↦ b * x) = fun x ↦ 0 + b * x := funext fun x ↦ (zero_add _).symm
  rw [inverseGaussianMeasure_eq_withDensity, hfun, map_affine_withDensity_volume _ hb.ne',
    inverseGaussianMeasure_eq_withDensity]
  congr 1
  funext x
  rw [affineDensity_apply, inverseGaussianPDF_eq_ofReal, inverseGaussianPDF_eq_ofReal,
    inverseGaussianPDFReal_mul_mul hb, sub_zero, abs_of_pos hb,
    ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]

/-- The random-variable form of positive scaling of the inverse Gaussian law. -/
theorem hasLaw_inverseGaussianMeasure_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {b : ℝ} (hb : 0 < b) (hX : HasLaw X (inverseGaussianMeasure μ lam) P) :
    HasLaw (fun ω ↦ b * X ω) (inverseGaussianMeasure (b * μ) (b * lam)) P :=
  (HasLaw.mk (by fun_prop) (inverseGaussianMeasure_map_const_mul hb μ lam)).fun_comp hX

end TauCeti.Probability
