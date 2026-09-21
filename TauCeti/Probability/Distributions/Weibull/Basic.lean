/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The Weibull distribution

The Weibull law with shape `k` and scale `lam` has density
`(k / lam) * (x / lam) ^ (k - 1) * exp (-(x / lam) ^ k)` on the positive
half-line. This file defines the law, proves that it is a probability measure exactly when both
parameters are positive, computes its cdf and all natural moments, and deduces its mean and
variance.

Invalid parameters produce the zero measure. This convention makes `weibullMeasure` a total,
jointly measurable family without pretending that a nonpositive shape or scale defines a
probability law.

On the positive half-line the density times `x ^ n` is a constant multiple of
`x ^ (k - 1 + n) * exp (-(lam ^ k)⁻¹ * x ^ k)`, so the total mass and every natural moment are
instances of Mathlib's scaled Gamma integral `integral_rpow_mul_exp_neg_mul_rpow`. The upper tail
follows from the antiderivative `-exp (-(x / lam) ^ k)` of the density.

## Main definitions and results

* `weibullPDFReal`, `weibullPDF` and `weibullMeasure` define the density and law;
* `weibullMeasure_def` exposes the defining `withDensity` equation, and
  `integrable_weibullMeasure_iff` and `integral_weibullMeasure_eq` transfer integrability and
  integrals against the law to the density;
* `isProbabilityMeasure_weibullMeasure_iff` characterizes the valid parameter range;
* `weibullMeasure_Iic_zero` and `ae_pos_weibullMeasure` record that every Weibull measure is
  concentrated on the positive half-line;
* `cdf_weibullMeasure_eq` gives the closed cdf;
* `integral_pow_weibullMeasure` gives every natural moment;
* `integral_id_weibullMeasure` and `variance_id_weibullMeasure` give the mean and variance;
* `weibullMeasure_one_eq_expMeasure` identifies shape-one Weibull laws with exponential laws;
* `measurable_weibullMeasure` makes the family available for kernel constructions.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Weibull**.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Nat Topology

namespace TauCeti

namespace Probability

variable {k lam x : ℝ}

/-! ### Density and measure -/

/-- The real-valued Weibull density with shape `k` and scale `lam`.

It is defined to be zero unless `k`, `lam`, and the sample point are all positive. -/
def weibullPDFReal (k lam x : ℝ) : ℝ :=
  if 0 < k ∧ 0 < lam ∧ 0 < x then
    (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)
  else 0

/-- The Weibull density, valued in `ℝ≥0∞`. -/
def weibullPDF (k lam x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (weibullPDFReal k lam x)

/-- The Weibull law with shape `k` and scale `lam`.

For invalid parameters this is the zero measure. -/
def weibullMeasure (k lam : ℝ) : Measure ℝ :=
  volume.withDensity (weibullPDF k lam)

/-- A Weibull measure is Lebesgue measure weighted by its density.

This exposes the defining equation of the opaque public definition, whose body cannot be unfolded
outside this module; `integrable_weibullMeasure_iff` and `integral_weibullMeasure_eq` are the
derived forms a consumer usually wants. -/
theorem weibullMeasure_def (k lam : ℝ) :
    weibullMeasure k lam = volume.withDensity (weibullPDF k lam) := by
  rfl

/-- The `ℝ≥0∞`-valued density is the nonnegative coercion of the real density. -/
theorem weibullPDF_eq_ofReal (k lam x : ℝ) :
    weibullPDF k lam x = ENNReal.ofReal (weibullPDFReal k lam x) := by
  rw [weibullPDF]

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem weibullPDFReal_of_pos (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    weibullPDFReal k lam x =
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k) := by
  simp [weibullPDFReal, hk, hlam, hx]

/-- The density vanishes on the nonpositive half-line. -/
@[simp]
theorem weibullPDFReal_of_nonpos (hx : x ≤ 0) (k lam : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hx]

/-- The density vanishes when the shape is nonpositive. -/
@[simp]
theorem weibullPDFReal_of_shape_nonpos (hk : k ≤ 0) (lam x : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hk]

/-- The density vanishes when the scale is nonpositive. -/
@[simp]
theorem weibullPDFReal_of_scale_nonpos (hlam : lam ≤ 0) (k x : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hlam]

/-- The `ℝ≥0∞`-valued density vanishes on the nonpositive half-line. -/
@[simp]
theorem weibullPDF_of_nonpos (hx : x ≤ 0) (k lam : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes when the shape is nonpositive. -/
@[simp]
theorem weibullPDF_of_shape_nonpos (hk : k ≤ 0) (lam x : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_shape_nonpos hk, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes when the scale is nonpositive. -/
@[simp]
theorem weibullPDF_of_scale_nonpos (hlam : lam ≤ 0) (k x : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_scale_nonpos hlam, ENNReal.ofReal_zero]

/-- At valid parameters and a positive point, the `ℝ≥0∞` density has the usual formula. -/
@[simp]
theorem weibullPDF_of_pos (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    weibullPDF k lam x = ENNReal.ofReal
      ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_pos hk hlam hx]

/-- The real-valued Weibull density is nonnegative. -/
theorem weibullPDFReal_nonneg (k lam x : ℝ) : 0 ≤ weibullPDFReal k lam x := by
  rw [weibullPDFReal]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (div_nonneg h.1.le h.2.1.le)
      (Real.rpow_nonneg (div_nonneg h.2.2.le h.2.1.le) _)) (Real.exp_pos _).le
  · exact le_rfl

/-- At valid parameters the density is strictly positive precisely on the positive half-line. -/
theorem weibullPDFReal_pos_iff (hk : 0 < k) (hlam : 0 < lam) :
    0 < weibullPDFReal k lam x ↔ 0 < x := by
  constructor
  · contrapose!
    intro hx
    rw [weibullPDFReal_of_nonpos hx k lam]
  · intro hx
    rw [weibullPDFReal_of_pos hk hlam hx]
    positivity

/-- The two density representations agree under `ENNReal.toReal`. -/
@[simp]
theorem toReal_weibullPDF (k lam x : ℝ) :
    (weibullPDF k lam x).toReal = weibullPDFReal k lam x :=
  ENNReal.toReal_ofReal (weibullPDFReal_nonneg k lam x)

/-- The real Weibull density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_weibullPDFReal (k lam : ℝ) : Measurable (weibullPDFReal k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rcases hvalid with ⟨hk, hlam⟩
    have heq : weibullPDFReal k lam = fun x ↦
        if 0 < x then (k / lam) * Real.exp (Real.log (x / lam) * (k - 1)) *
          Real.exp (-Real.exp (Real.log (x / lam) * k)) else 0 := by
      funext x
      by_cases hx : 0 < x
      · rw [weibullPDFReal_of_pos hk hlam hx, ite_eq_left hx,
          Real.rpow_def_of_pos (div_pos hx hlam), Real.rpow_def_of_pos (div_pos hx hlam)]
      · rw [weibullPDFReal_of_nonpos (not_lt.mp hx) k lam, ite_eq_right hx]
    rw [heq]
    refine Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
      measurable_const
  · have heq : weibullPDFReal k lam = 0 := by
      funext x
      rw [weibullPDFReal]
      simp only [Pi.zero_apply]
      exact ite_eq_right (fun hx ↦ hvalid ⟨hx.1, hx.2.1⟩)
    rw [heq]
    fun_prop

/-- The `ℝ≥0∞`-valued Weibull density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_weibullPDF (k lam : ℝ) : Measurable (weibullPDF k lam) :=
  (measurable_weibullPDFReal k lam).ennreal_ofReal

/-- If either parameter is invalid, the Weibull measure is zero. -/
@[simp]
theorem weibullMeasure_of_not_pos (h : ¬ (0 < k ∧ 0 < lam)) : weibullMeasure k lam = 0 := by
  have hpdf : weibullPDF k lam = 0 := by
    funext y
    simp only [weibullPDF, weibullPDFReal]
    rw [ite_eq_right (fun hy ↦ h ⟨hy.1, hy.2.1⟩), ENNReal.ofReal_zero]
    rfl
  rw [weibullMeasure, hpdf, withDensity_zero]

/-- A Weibull measure gives no mass to the nonpositive half-line. This also holds at invalid
parameters, where the measure is zero. -/
@[simp]
theorem weibullMeasure_Iic_zero (k lam : ℝ) : weibullMeasure k lam (Iic 0) = 0 := by
  rw [weibullMeasure, withDensity_apply _ measurableSet_Iic]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  simpa only [Pi.zero_apply] using weibullPDF_of_nonpos hx k lam

/-- A Weibull random variable is almost surely positive. This remains true vacuously at invalid
parameters, where `weibullMeasure` is the zero measure. -/
theorem ae_pos_weibullMeasure (k lam : ℝ) : ∀ᵐ x ∂weibullMeasure k lam, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using weibullMeasure_Iic_zero k lam

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against a Weibull measure exactly when
its density-weighted version is Lebesgue integrable. This holds at every parameter, the zero
measure included, and is the form in which downstream files should meet `weibullMeasure`. -/
theorem integrable_weibullMeasure_iff (k lam : ℝ) {g : ℝ → E} :
    Integrable g (weibullMeasure k lam) ↔
      Integrable (fun x ↦ weibullPDFReal k lam x • g x) := by
  rw [weibullMeasure_def, funext (weibullPDF_eq_ofReal k lam)]
  exact Probability.integrable_withDensity_ofReal_iff (measurable_weibullPDFReal k lam).aemeasurable
    (ae_of_all _ (weibullPDFReal_nonneg k lam))

/-- **Integral transfer.** An integral against a Weibull measure is the density-weighted Lebesgue
integral. This holds at every parameter, the zero measure included. -/
theorem integral_weibullMeasure_eq (k lam : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂weibullMeasure k lam = ∫ x, weibullPDFReal k lam x • g x := by
  rw [weibullMeasure_def, funext (weibullPDF_eq_ofReal k lam)]
  exact Probability.integral_withDensity_ofReal (measurable_weibullPDFReal k lam).aemeasurable
    (ae_of_all _ (weibullPDFReal_nonneg k lam)) g

end Transfer

/-! ### Normalization, natural-power integrals, and tails -/

/-- On the positive half-line, the density times `x ^ n` is a constant multiple of the integrand
of the scaled Gamma integral `integral_rpow_mul_exp_neg_mul_rpow`, with rate `(lam ^ k)⁻¹`. -/
private lemma weibullPDFReal_mul_pow_eq (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) (n : ℕ) :
    weibullPDFReal k lam x * x ^ n =
      k / lam ^ k * (x ^ (k - 1 + (n : ℝ)) * Real.exp (-(lam ^ k)⁻¹ * x ^ k)) := by
  have hexp : -(x / lam) ^ k = -(lam ^ k)⁻¹ * x ^ k := by
    rw [Real.div_rpow hx.le hlam.le]
    ring
  rw [weibullPDFReal_of_pos hk hlam hx, hexp, Real.div_rpow hx.le hlam.le,
    Real.rpow_sub_one hlam.ne', Real.rpow_add_natCast hx.ne']
  field_simp

/-- The density times `x ^ n` vanishes off the positive half-line. -/
private lemma weibullPDFReal_mul_pow_of_notMem (hx : x ∉ Ioi 0) (k lam : ℝ) (n : ℕ) :
    weibullPDFReal k lam x * x ^ n = 0 := by
  rw [weibullPDFReal_of_nonpos (not_lt.mp hx), zero_mul]

/-- The density weighted by a natural power is integrable at valid parameters. -/
private lemma integrable_weibullPDFReal_mul_pow (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    Integrable (fun y ↦ weibullPDFReal k lam y * y ^ n) := by
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow (s := k - 1 + (n : ℝ))
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hk (inv_pos.mpr (Real.rpow_pos_of_pos hlam k))
  refine (integrableOn_iff_integrable_of_support_subset fun y hy ↦ ?_).mp
    (IntegrableOn.congr_fun (hbase.const_mul (k / lam ^ k))
      (fun y hy ↦ (weibullPDFReal_mul_pow_eq hk hlam hy n).symm) measurableSet_Ioi)
  by_contra hy'
  exact hy (weibullPDFReal_mul_pow_of_notMem hy' k lam n)

/-- The density weighted by `y ^ n` integrates to the `n`th Weibull moment. -/
private lemma integral_weibullPDFReal_mul_pow (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    ∫ y, weibullPDFReal k lam y * y ^ n = lam ^ n * Real.Gamma (1 + (n : ℝ) / k) := by
  have hexp : (k - 1 + (n : ℝ) + 1) / k = 1 + (n : ℝ) / k := by
    field_simp
    ring
  have hrate : ((lam ^ k)⁻¹) ^ (-(k - 1 + (n : ℝ) + 1) / k) = lam ^ k * lam ^ n := by
    rw [Real.inv_rpow (Real.rpow_nonneg hlam.le k), ← Real.rpow_neg (Real.rpow_nonneg hlam.le k),
      ← Real.rpow_mul hlam.le, ← Real.rpow_natCast, ← Real.rpow_add hlam]
    congr 1
    field_simp
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      fun y hy ↦ weibullPDFReal_mul_pow_of_notMem hy k lam n,
    setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ weibullPDFReal_mul_pow_eq hk hlam hy n,
    integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow hk
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (inv_pos.mpr (Real.rpow_pos_of_pos hlam k)), hrate, hexp]
  field_simp

/-- The real density is integrable for all parameters. -/
theorem integrable_weibullPDFReal (k lam : ℝ) : Integrable (weibullPDFReal k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · simpa using integrable_weibullPDFReal_mul_pow hvalid.1 hvalid.2 0
  · have hzero : weibullPDFReal k lam = fun _ ↦ 0 := by
      funext z
      simp only [weibullPDFReal]
      rw [ite_eq_right (fun hz ↦ hvalid ⟨hz.1, hz.2.1⟩)]
    rw [hzero]
    exact integrable_zero ℝ ℝ volume

/-- The real Weibull density has total mass one at valid parameters. -/
theorem integral_weibullPDFReal (hk : 0 < k) (hlam : 0 < lam) :
    ∫ y, weibullPDFReal k lam y = 1 := by
  simpa using integral_weibullPDFReal_mul_pow hk hlam 0

/-- The `ℝ≥0∞`-valued Weibull density has total mass one. -/
theorem lintegral_weibullPDF_eq_one (hk : 0 < k) (hlam : 0 < lam) :
    ∫⁻ y, weibullPDF k lam y = 1 := by
  simp_rw [weibullPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weibullPDFReal k lam)
      (ae_of_all _ fun y ↦ weibullPDFReal_nonneg k lam y),
    integral_weibullPDFReal hk hlam, ENNReal.ofReal_one]

/-- For positive shape and scale the Weibull law is a probability measure. -/
theorem isProbabilityMeasure_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    IsProbabilityMeasure (weibullMeasure k lam) := by
  constructor
  rw [weibullMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_weibullPDF_eq_one hk hlam]

/-- The Weibull law is a probability measure exactly for positive shape and scale. -/
@[simp]
theorem isProbabilityMeasure_weibullMeasure_iff :
    IsProbabilityMeasure (weibullMeasure k lam) ↔ 0 < k ∧ 0 < lam := by
  constructor
  · intro hp
    by_contra h
    rw [weibullMeasure_of_not_pos h] at hp
    have hone : (0 : Measure ℝ) Set.univ = 1 :=
      @IsProbabilityMeasure.measure_univ ℝ _ (0 : Measure ℝ) hp
    have hzero_eq_one : (0 : ℝ≥0∞) = 1 := hone
    exact zero_ne_one hzero_eq_one
  · rintro ⟨hk, hlam⟩
    exact isProbabilityMeasure_weibullMeasure hk hlam

/-- Every Weibull measure is finite, including the zero measure at invalid parameters. -/
instance : IsFiniteMeasure (weibullMeasure k lam) := by
  by_cases h : 0 < k ∧ 0 < lam
  · let _ : IsProbabilityMeasure (weibullMeasure k lam) :=
      isProbabilityMeasure_weibullMeasure h.1 h.2
    infer_instance
  · rw [weibullMeasure_of_not_pos h]
    infer_instance

/-- The upper tail integral of a valid Weibull density. -/
theorem integral_weibullPDFReal_Ioi (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    ∫ y in Ioi x, weibullPDFReal k lam y = Real.exp (-(x / lam) ^ k) := by
  -- `-exp (-(y / lam) ^ k)` is an antiderivative of the density on the positive half-line.
  have hderiv : ∀ y ∈ Ici x,
      HasDerivAt (fun z ↦ -Real.exp (-(z / lam) ^ k)) (weibullPDFReal k lam y) y := by
    intro y hy
    have hy0 : 0 < y := hx.trans_le hy
    have hpow := ((hasDerivAt_id y).div_const lam).rpow_const (p := k)
      (Or.inl (div_pos hy0 hlam).ne')
    rw [weibullPDFReal_of_pos hk hlam hy0]
    refine hpow.neg.exp.neg.congr_deriv ?_
    simp only [Pi.neg_apply, id_eq]
    ring
  have hlim : Tendsto (fun z ↦ -Real.exp (-(z / lam) ^ k)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_rpow_atTop hk).comp (tendsto_id.atTop_div_const hlam))).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrable_weibullPDFReal k lam).integrableOn
    hlim, zero_sub, neg_neg]

/-! ### Density interface and cumulative distribution function -/

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {X : Omega → ℝ}

/-- A random variable with a Weibull law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_weibullPDF k lam).aemeasurable hX

/-- The density of a random variable with a Weibull law is `weibullPDF`. -/
theorem pdf_eq_weibullPDF_of_hasLaw_weibullMeasure
    (hX : HasLaw X (weibullMeasure k lam) P) :
    pdf X P volume =ᵐ[volume] weibullPDF k lam :=
  pdf_eq_of_hasLaw_withDensity (measurable_weibullPDF k lam).aemeasurable hX

/-- The Radon–Nikodym derivative of a Weibull law is its density. -/
theorem rnDeriv_weibullMeasure (k lam : ℝ) :
    (weibullMeasure k lam).rnDeriv volume =ᵐ[volume] weibullPDF k lam :=
  Measure.rnDeriv_withDensity volume (measurable_weibullPDF k lam)

/-- Integrating the density computes the real mass of a measurable set. -/
private lemma measureReal_weibullMeasure {s : Set ℝ} (hs : MeasurableSet s) :
    (weibullMeasure k lam).real s = ∫ y in s, weibullPDFReal k lam y := by
  rw [weibullMeasure_def, funext (weibullPDF_eq_ofReal k lam)]
  exact Probability.measureReal_withDensity_ofReal (ae_of_all _ (weibullPDFReal_nonneg k lam)) hs
    (integrable_weibullPDFReal k lam).integrableOn

/-- The real upper-tail mass of a valid Weibull law. -/
theorem measureReal_Ioi_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    (weibullMeasure k lam).real (Ioi x) = Real.exp (-(x / lam) ^ k) := by
  rw [measureReal_weibullMeasure measurableSet_Ioi,
    integral_weibullPDFReal_Ioi hk hlam hx]

/-- The cdf of a valid Weibull law. -/
theorem cdf_weibullMeasure_eq (hk : 0 < k) (hlam : 0 < lam) (x : ℝ) :
    cdf (weibullMeasure k lam) x =
      if x ≤ 0 then 0 else 1 - Real.exp (-(x / lam) ^ k) := by
  have hp : IsProbabilityMeasure (weibullMeasure k lam) :=
    isProbabilityMeasure_weibullMeasure hk hlam
  rw [cdf_eq_real]
  split_ifs with hx
  · rw [measureReal_weibullMeasure measurableSet_Iic]
    exact integral_eq_zero_of_ae (ae_restrict_mem measurableSet_Iic |>.mono
      fun y hy ↦ weibullPDFReal_of_nonpos (hy.trans hx) k lam)
  · rw [← compl_Ioi, measureReal_compl measurableSet_Ioi,
      measureReal_Ioi_weibullMeasure hk hlam (not_le.mp hx)]
    simp

/-- At shape one and positive scale, the Weibull cdf is the cdf of the exponential law of rate
`lam⁻¹`. Kept private: `weibullMeasure_one_eq_expMeasure` upgrades it to an identity of measures
that needs no positivity and rewrites every cdf occurrence directly. -/
private lemma cdf_weibullMeasure_one_eq_cdf_expMeasure_of_pos (hlam : 0 < lam) (x : ℝ) :
    cdf (weibullMeasure 1 lam) x = cdf (expMeasure lam⁻¹) x := by
  rw [cdf_weibullMeasure_eq one_pos hlam, cdf_expMeasure_eq (inv_pos.mpr hlam)]
  by_cases hx : x ≤ 0
  · rcases lt_or_eq_of_le hx with hxlt | rfl
    · simp [hx, not_le.mpr hxlt]
    · simp
  · have hx' : 0 ≤ x := (not_le.mp hx).le
    simp only [ite_eq_right hx, ite_eq_left hx', Real.rpow_one]
    congr 3
    field_simp

/-- **A shape-one Weibull law is exponential.** Its scale `lam` is the reciprocal of the
exponential rate. No positivity is needed: at a nonpositive scale both sides are the zero
measure, since the exponential law is the shape-one Gamma law, whose density is `ENNReal.ofReal`
of a nonpositive quantity at a nonpositive rate. -/
@[simp]
theorem weibullMeasure_one_eq_expMeasure (lam : ℝ) :
    weibullMeasure 1 lam = expMeasure lam⁻¹ := by
  rcases le_or_gt lam 0 with hlam | hlam
  -- The zero branch stays inside the Gamma presentation: `expMeasure` unfolds to `gammaMeasure 1`,
  -- so its density is `gammaPDF 1`, and no bridge between two density presentations is needed.
  · have hpdf : gammaPDF 1 lam⁻¹ = 0 := by
      funext y
      rw [gammaPDF_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero]
      simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
      split_ifs
      · exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hlam) (Real.exp_pos _).le
      · exact le_rfl
    have hexp : expMeasure lam⁻¹ = 0 := by
      rw [expMeasure, gammaMeasure, hpdf, withDensity_zero]
    rw [weibullMeasure_of_not_pos fun h ↦ absurd h.2 (not_lt.mpr hlam), hexp]
  · let _ : IsProbabilityMeasure (weibullMeasure 1 lam) :=
      isProbabilityMeasure_weibullMeasure one_pos hlam
    let _ : IsProbabilityMeasure (expMeasure lam⁻¹) :=
      isProbabilityMeasure_expMeasure (inv_pos.mpr hlam)
    apply Measure.eq_of_cdf
    ext x
    exact cdf_weibullMeasure_one_eq_cdf_expMeasure_of_pos hlam x

/-! ### Natural moments, mean, and variance -/

/-- Every natural power is integrable under a Weibull measure. -/
theorem integrable_pow_weibullMeasure (k lam : ℝ) (n : ℕ) :
    Integrable (fun y ↦ y ^ n) (weibullMeasure k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rcases hvalid with ⟨hk, hlam⟩
    rw [integrable_weibullMeasure_iff]
    simp_rw [smul_eq_mul]
    exact integrable_weibullPDFReal_mul_pow hk hlam n
  · simp [weibullMeasure_of_not_pos hvalid]

/-- The `n`th raw moment of a valid Weibull law. -/
@[simp]
theorem integral_pow_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    ∫ y, y ^ n ∂weibullMeasure k lam =
      lam ^ n * Real.Gamma (1 + (n : ℝ) / k) := by
  rw [integral_weibullMeasure_eq]
  simp_rw [smul_eq_mul]
  exact integral_weibullPDFReal_mul_pow hk hlam n

/-- The mean of a valid Weibull law. -/
@[simp]
theorem integral_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    ∫ y, y ∂weibullMeasure k lam = lam * Real.Gamma (1 + 1 / k) := by
  simpa using integral_pow_weibullMeasure hk hlam 1

/-- The variance of a valid Weibull law. -/
theorem variance_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    variance id (weibullMeasure k lam) =
      lam ^ 2 * (Real.Gamma (1 + 2 / k) - Real.Gamma (1 + 1 / k) ^ 2) := by
  have hp : IsProbabilityMeasure (weibullMeasure k lam) :=
    isProbabilityMeasure_weibullMeasure hk hlam
  have hmem : MemLp id 2 (weibullMeasure k lam) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (by simpa using integrable_pow_weibullMeasure k lam 2)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_pow_weibullMeasure hk hlam,
    integral_id_weibullMeasure hk hlam]
  ring_nf

/-! ### Parameter measurability -/

/-- The Weibull density is jointly measurable in shape, scale, and sample point. -/
@[fun_prop]
theorem measurable_uncurry_weibullPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ weibullPDF q.1.1 q.1.2 q.2 := by
  have heq : (fun q : (ℝ × ℝ) × ℝ ↦ weibullPDF q.1.1 q.1.2 q.2) = fun q ↦
      ENNReal.ofReal (if 0 < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2 then
        (q.1.1 / q.1.2) * Real.exp (Real.log (q.2 / q.1.2) * (q.1.1 - 1)) *
          Real.exp (-Real.exp (Real.log (q.2 / q.1.2) * q.1.1)) else 0) := by
    funext q
    rw [weibullPDF, weibullPDFReal]
    split_ifs with h
    · rw [Real.rpow_def_of_pos (div_pos h.2.2 h.2.1),
        Real.rpow_def_of_pos (div_pos h.2.2 h.2.1)]
    · rfl
  rw [heq]
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  have hkset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.1} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_fst.fst
  have hlamset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.2} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_fst.snd
  have hxset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.2} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_snd
  have hset : {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2} =
      {q | (0 : ℝ) < q.1.1} ∩ {q | (0 : ℝ) < q.1.2} ∩ {q | (0 : ℝ) < q.2} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact and_assoc.symm
  rw [hset]
  exact (hkset.inter hlamset).inter hxset

/-- The Weibull family is measurable in shape and scale. -/
@[fun_prop]
theorem measurable_weibullMeasure :
    Measurable fun p : ℝ × ℝ ↦ weibullMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_weibullPDF

end Probability

end TauCeti
