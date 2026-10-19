/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Distributions.Uniform.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import TauCeti.Analysis.SpecialFunctions.Sigmoid
import TauCeti.MeasureTheory.Integral.ExpDecay
import TauCeti.Probability.Distributions.Affine
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The logistic distribution

The logistic law with location `m` and scale `s > 0` is the law of `m + s * log (U / (1 - U))`
for `U` uniform on the unit interval, and it is *defined* here as that pushforward of
`uniformMeasure 0 1`. Writing `y = (x - m) / s`, its cumulative distribution function is the
sigmoid `Real.sigmoid y = (1 + exp (-y))⁻¹`, its density is
`exp (-y) / (s * (1 + exp (-y)) ^ 2)`, and its quantile function is
`u ↦ m + s * log (u / (1 - u))`, the map the law was defined by.

**Boundary.** For `s ≤ 0` there is no logistic law: `logisticMeasure m s` and its density are
*defined* to vanish there (`logisticMeasure_of_nonpos`, `logisticPDFReal_of_nonpos`). The
density presentation `logisticMeasure_eq_withDensity` and the affine transport
`map_affine_logisticMeasure` hold at every parameter, which is what makes the family measurable
in its parameters with no case split.

## Main definitions

* `TauCeti.Probability.logisticPDFReal` — the real-valued density;
* `TauCeti.Probability.logisticPDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.logisticMeasure` — the law, as the image of the standard uniform law under
  `u ↦ m + s * log (u / (1 - u))`.

## Main results

* `isProbabilityMeasure_logisticMeasure` — it is a probability measure when `0 < s`;
* `hasLaw_logisticMeasure_of_hasLaw_uniformMeasure` — the logit of a standard uniform variable,
  scaled and shifted, has the logistic law;
* `cdf_logisticMeasure_eq` — the cdf is `Real.sigmoid ((x - m) / s)`;
* `logisticMeasure_eq_withDensity`, `hasPDF_of_hasLaw_logisticMeasure`,
  `pdf_eq_logisticPDF_of_hasLaw_logisticMeasure` and `rnDeriv_logisticMeasure` — the density;
* `quantile_logisticMeasure` — the quantile is `m + s * log (u / (1 - u))`;
* `map_affine_logisticMeasure` — the affine image `a + b X` of a logistic variable `X` with
  `b ≠ 0` is logistic with location `a + b * m` and scale `|b| * s`;
* `measurable_logisticMeasure` — the family is measurable in its two parameters.

## Implementation

The cdf is computed from the definition: on the open unit interval the logit is strictly
increasing with inverse `Real.sigmoid` (`Real.log_div_one_sub_le_iff`), so the event
`{m + s * log (U / (1 - U)) ≤ x}` is `{U ≤ sigmoid ((x - m) / s)}` up to the null endpoint `1`.
The density is the derivative of that cdf, so the fundamental theorem of calculus on `Set.Iic x`
shows that `volume.withDensity logisticPDF` has the same cdf, and two finite measures on `ℝ` with
the same cdf agree (`MeasureTheory.Measure.ext_of_Iic`). Affine transport goes through the density
and `TauCeti.Probability.map_affine_withDensity_volume`; at a negative slope it uses that the
standardized density `sigmoid y * (1 - sigmoid y)` is even.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 23.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m s x : ℝ}

/-! ### The density -/

/-- The density of the logistic law with location `m` and scale `s`, as a real-valued function:
`exp (-y) / (s * (1 + exp (-y)) ^ 2)` with `y = (x - m) / s`.

For `s ≤ 0` there is no such law and the density is `0`. -/
def logisticPDFReal (m s x : ℝ) : ℝ :=
  if 0 < s then Real.exp (-((x - m) / s)) / (s * (1 + Real.exp (-((x - m) / s))) ^ 2) else 0

/-- The density of the logistic law, as a function valued in `ℝ≥0∞`. -/
def logisticPDF (m s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logisticPDFReal m s x)

/-- The `ℝ≥0∞`-valued logistic density is the coercion of the real-valued one. -/
theorem logisticPDF_eq_ofReal (m s x : ℝ) :
    logisticPDF m s x = ENNReal.ofReal (logisticPDFReal m s x) := by
  rw [logisticPDF]

/-- Outside the valid parameter range the density vanishes. -/
@[simp]
theorem logisticPDFReal_of_nonpos (hs : s ≤ 0) (m x : ℝ) : logisticPDFReal m s x = 0 := by
  rw [logisticPDFReal, ite_eq_right (not_lt.mpr hs)]

/-- For a positive scale the density is `exp (-y) / (s * (1 + exp (-y)) ^ 2)` with
`y = (x - m) / s`. -/
@[simp]
theorem logisticPDFReal_of_pos (hs : 0 < s) (m x : ℝ) :
    logisticPDFReal m s x =
      Real.exp (-((x - m) / s)) / (s * (1 + Real.exp (-((x - m) / s))) ^ 2) := by
  rw [logisticPDFReal, ite_eq_left hs]

/-- For a positive scale the density is `σ (1 - σ) / s` for the sigmoid `σ` at `(x - m) / s`,
that is, the derivative of the cdf `x ↦ Real.sigmoid ((x - m) / s)`. -/
theorem logisticPDFReal_eq_sigmoid (hs : 0 < s) (m x : ℝ) :
    logisticPDFReal m s x =
      Real.sigmoid ((x - m) / s) * (1 - Real.sigmoid ((x - m) / s)) / s := by
  rw [logisticPDFReal_of_pos hs, Real.sigmoid_mul_one_sub_sigmoid, div_div, mul_comm s]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem logisticPDF_of_nonpos (hs : s ≤ 0) (m x : ℝ) : logisticPDF m s x = 0 := by
  rw [logisticPDF_eq_ofReal, logisticPDFReal_of_nonpos hs, ENNReal.ofReal_zero]

/-- For a positive scale the `ℝ≥0∞`-valued density is the coercion of
`exp (-y) / (s * (1 + exp (-y)) ^ 2)` with `y = (x - m) / s`. -/
@[simp]
theorem logisticPDF_of_pos (hs : 0 < s) (m x : ℝ) :
    logisticPDF m s x = ENNReal.ofReal
      (Real.exp (-((x - m) / s)) / (s * (1 + Real.exp (-((x - m) / s))) ^ 2)) := by
  rw [logisticPDF_eq_ofReal, logisticPDFReal_of_pos hs]

/-- The logistic density is nonnegative at every parameter, valid or not. -/
theorem logisticPDFReal_nonneg (m s x : ℝ) : 0 ≤ logisticPDFReal m s x := by
  rcases le_or_gt s 0 with hs | hs
  · rw [logisticPDFReal_of_nonpos hs]
  · rw [logisticPDFReal_of_pos hs]
    positivity

/-- For a positive scale the logistic density is strictly positive everywhere. -/
theorem logisticPDFReal_pos (hs : 0 < s) (m x : ℝ) : 0 < logisticPDFReal m s x := by
  rw [logisticPDFReal_of_pos hs]
  positivity

/-- The two logistic densities agree under `ENNReal.toReal`; the density is never infinite. -/
@[simp]
theorem toReal_logisticPDF (m s x : ℝ) : (logisticPDF m s x).toReal = logisticPDFReal m s x :=
  ENNReal.toReal_ofReal (logisticPDFReal_nonneg m s x)

/-- The logistic density is measurable jointly in its location, its scale and the point. -/
@[fun_prop]
theorem measurable_uncurry_logisticPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ => logisticPDFReal q.1.1 q.1.2 q.2 := by
  simp only [logisticPDFReal]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd) (by fun_prop)
    measurable_const

/-- The `ℝ≥0∞`-valued logistic density is measurable jointly in its parameters and the point. -/
@[fun_prop]
theorem measurable_uncurry_logisticPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => logisticPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_logisticPDFReal.ennreal_ofReal

/-- The real-valued logistic density is measurable. -/
@[fun_prop]
theorem measurable_logisticPDFReal (m s : ℝ) : Measurable (logisticPDFReal m s) :=
  measurable_uncurry_logisticPDFReal.comp (measurable_prodMk_left (x := (m, s)))

/-- The `ℝ≥0∞`-valued logistic density is measurable. -/
@[fun_prop]
theorem measurable_logisticPDF (m s : ℝ) : Measurable (logisticPDF m s) :=
  (measurable_logisticPDFReal m s).ennreal_ofReal

/-- The logistic density has exponentially decaying tails: it is at most
`s⁻¹ * exp (-(s⁻¹ * |x - m|))`. -/
private lemma logisticPDFReal_le (hs : 0 < s) (m x : ℝ) :
    logisticPDFReal m s x ≤ s⁻¹ * Real.exp (-(s⁻¹ * |x - m|)) := by
  have key : ∀ y : ℝ, Real.sigmoid y * (1 - Real.sigmoid y) ≤ Real.exp (-y) := fun y => by
    rw [Real.sigmoid_mul_one_sub_sigmoid]
    refine div_le_self (Real.exp_pos _).le ?_
    nlinarith [Real.exp_pos (-y)]
  have hy : s⁻¹ * |x - m| = |(x - m) / s| := by
    rw [abs_div, abs_of_pos hs, inv_mul_eq_div]
  rw [logisticPDFReal_eq_sigmoid hs, div_eq_inv_mul, hy]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hs.le)
  rcases le_total 0 ((x - m) / s) with h | h
  · rw [abs_of_nonneg h]
    exact key _
  · have h' := key (-((x - m) / s))
    rwa [Real.sigmoid_neg, sub_sub_cancel, mul_comm, ← abs_of_nonpos h] at h'

/-- The logistic density is integrable on the whole line for every scale. -/
theorem integrable_logisticPDFReal (m s : ℝ) : Integrable (logisticPDFReal m s) := by
  rcases le_or_gt s 0 with hs | hs
  · have h : logisticPDFReal m s = fun _ => 0 := funext (logisticPDFReal_of_nonpos hs m)
    rw [h]
    exact integrable_zero ℝ ℝ volume
  · have hdom : Integrable fun x : ℝ => s⁻¹ * Real.exp (-(s⁻¹ * |x - m|)) :=
      ((TauCeti.integrable_exp_neg_mul_abs (inv_pos.mpr hs)).comp_sub_right m).const_mul _
    refine hdom.mono' (measurable_logisticPDFReal m s).aestronglyMeasurable
      (.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (logisticPDFReal_nonneg m s x)]
    exact logisticPDFReal_le hs m x

/-- The derivative of the logistic cdf `x ↦ Real.sigmoid ((x - m) / s)` is the logistic
density. -/
theorem hasDerivAt_sigmoid_logisticPDFReal (hs : 0 < s) (m x : ℝ) :
    HasDerivAt (fun y => Real.sigmoid ((y - m) / s)) (logisticPDFReal m s x) x := by
  have h := (Real.hasDerivAt_sigmoid ((x - m) / s)).comp x
    (((hasDerivAt_id x).sub_const m).div_const s)
  rw [logisticPDFReal_eq_sigmoid hs, div_eq_mul_one_div _ s]
  exact h

/-- The mass of the logistic density below a point is the sigmoid of the standardized point. -/
theorem integral_logisticPDFReal_Iic (hs : 0 < s) (m x : ℝ) :
    ∫ y in Iic x, logisticPDFReal m s y = Real.sigmoid ((x - m) / s) := by
  have hlim : Tendsto (fun y => Real.sigmoid ((y - m) / s)) atBot (𝓝 0) :=
    Real.tendsto_sigmoid_atBot.comp
      ((tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs)
  rw [integral_Iic_of_hasDerivAt_of_tendsto
      ((hasDerivAt_sigmoid_logisticPDFReal hs m x).continuousAt.continuousWithinAt)
      (fun y _ => hasDerivAt_sigmoid_logisticPDFReal hs m y)
      (integrable_logisticPDFReal m s).integrableOn hlim, sub_zero]

/-! ### The measure -/

/-- The logistic probability measure with location `m` and scale `s`: the law of
`m + s * log (U / (1 - U))` for `U` uniform on the unit interval.

For `s ≤ 0` this is the zero measure, not a probability measure; see
`logisticMeasure_of_nonpos`. -/
def logisticMeasure (m s : ℝ) : Measure ℝ :=
  if 0 < s then (uniformMeasure 0 1).map fun u => m + s * Real.log (u / (1 - u)) else 0

/-- For a positive scale the logistic law is the image of the standard uniform law under
`u ↦ m + s * log (u / (1 - u))`. -/
theorem logisticMeasure_of_pos (hs : 0 < s) (m : ℝ) :
    logisticMeasure m s = (uniformMeasure 0 1).map fun u => m + s * Real.log (u / (1 - u)) := by
  rw [logisticMeasure, ite_eq_left hs]

/-- Outside the valid parameter range the logistic law is the zero measure. -/
@[simp]
theorem logisticMeasure_of_nonpos (hs : s ≤ 0) (m : ℝ) : logisticMeasure m s = 0 := by
  rw [logisticMeasure, ite_eq_right (not_lt.mpr hs)]

/-- For a positive scale the logistic law is a probability measure. -/
theorem isProbabilityMeasure_logisticMeasure (hs : 0 < s) (m : ℝ) :
    IsProbabilityMeasure (logisticMeasure m s) := by
  rw [logisticMeasure_of_pos hs]
  infer_instance

/-- **The logistic law from a uniform variable.** If `U` is uniform on the unit interval, then
`m + s * log (U / (1 - U))` has the logistic law with location `m` and scale `s > 0`. -/
theorem hasLaw_logisticMeasure_of_hasLaw_uniformMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → ℝ} (hs : 0 < s) (m : ℝ) (hU : HasLaw U (uniformMeasure 0 1) P) :
    HasLaw (fun ω => m + s * Real.log (U ω / (1 - U ω))) (logisticMeasure m s) P := by
  rw [logisticMeasure_of_pos hs]
  exact (hasLaw_map (Real.measurable_logit_affine m s).aemeasurable).comp hU

/-- The logistic law of a lower half-line: the event `{X ≤ x}` has mass
`Real.sigmoid ((x - m) / s)`. -/
theorem logisticMeasure_Iic (hs : 0 < s) (m x : ℝ) :
    logisticMeasure m s (Iic x) = ENNReal.ofReal (Real.sigmoid ((x - m) / s)) := by
  have hunif : uniformMeasure 0 1 = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [uniformMeasure_eq_smul, sub_zero, ENNReal.ofReal_one, inv_one, one_smul]
    exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hpre : (fun u => m + s * Real.log (u / (1 - u))) ⁻¹' Iic x ∩ Ioo 0 1 =
      Ioc 0 (Real.sigmoid ((x - m) / s)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨hle, h0, h1⟩
      refine ⟨h0, (Real.log_div_one_sub_le_iff h0 h1).mp ?_⟩
      rw [le_div_iff₀ hs]
      linarith
    · rintro ⟨h0, hle⟩
      have h1 : u < 1 := hle.trans_lt (Real.sigmoid_lt_one _)
      refine ⟨?_, h0, h1⟩
      have := (Real.log_div_one_sub_le_iff h0 h1).mpr hle
      rw [le_div_iff₀ hs] at this
      linarith
  rw [logisticMeasure_of_pos hs,
    Measure.map_apply (Real.measurable_logit_affine m s) measurableSet_Iic, hunif,
    Measure.restrict_apply (Real.measurable_logit_affine m s measurableSet_Iic), hpre,
    Real.volume_Ioc, sub_zero]

/-- **The cdf of the logistic law** is the sigmoid of the standardized point:
`Real.sigmoid ((x - m) / s) = (1 + exp (-(x - m) / s))⁻¹`. -/
theorem cdf_logisticMeasure_eq (hs : 0 < s) (m x : ℝ) :
    cdf (logisticMeasure m s) x = Real.sigmoid ((x - m) / s) := by
  have := isProbabilityMeasure_logisticMeasure hs m
  rw [cdf_eq_real, measureReal_def, logisticMeasure_Iic hs,
    ENNReal.toReal_ofReal (Real.sigmoid_nonneg _)]

/-! ### The density of the measure -/

/-- **The density of the logistic law.** The logistic law is `volume.withDensity logisticPDF`, at
every parameter: for `s ≤ 0` both sides are zero. -/
theorem logisticMeasure_eq_withDensity (m s : ℝ) :
    logisticMeasure m s = volume.withDensity (logisticPDF m s) := by
  rcases le_or_gt s 0 with hs | hs
  · have h : logisticPDF m s = 0 := funext fun x => by
      rw [logisticPDF_of_nonpos hs, Pi.zero_apply]
    rw [logisticMeasure_of_nonpos hs, h, withDensity_zero]
  · have := isProbabilityMeasure_logisticMeasure hs m
    refine Measure.ext_of_Iic _ _ fun x => ?_
    have hpdf : logisticPDF m s = fun y => ENNReal.ofReal (logisticPDFReal m s y) :=
      funext (logisticPDF_eq_ofReal m s)
    rw [logisticMeasure_Iic hs, withDensity_apply _ measurableSet_Iic, hpdf,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_logisticPDFReal m s).integrableOn
        (.of_forall (logisticPDFReal_nonneg m s)), integral_logisticPDFReal_Iic hs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a logistic law has a density. -/
theorem hasPDF_of_hasLaw_logisticMeasure (hX : HasLaw X (logisticMeasure m s) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_logisticPDF m s).aemeasurable
    (by rwa [logisticMeasure_eq_withDensity] at hX)

/-- The density of a logistic law is `logisticPDF`. -/
theorem pdf_eq_logisticPDF_of_hasLaw_logisticMeasure (hX : HasLaw X (logisticMeasure m s) P) :
    pdf X P volume =ᵐ[volume] logisticPDF m s :=
  pdf_eq_of_hasLaw_withDensity (measurable_logisticPDF m s).aemeasurable
    (by rwa [logisticMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a logistic law against Lebesgue measure is `logisticPDF`. -/
theorem rnDeriv_logisticMeasure (m s : ℝ) :
    (logisticMeasure m s).rnDeriv volume =ᵐ[volume] logisticPDF m s := by
  rw [logisticMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_logisticPDF m s)

/-! ### The quantile function -/

/-- **The quantile function of the logistic law** is the map the law is defined by:
`u ↦ m + s * log (u / (1 - u))` at every level `0 < u < 1`. -/
theorem quantile_logisticMeasure (hs : 0 < s) (m : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (logisticMeasure m s).quantile u = m + s * Real.log (u / (1 - u)) := by
  have hcdf : cdf (logisticMeasure m s) (m + s * Real.log (u / (1 - u))) = u := by
    rw [cdf_logisticMeasure_eq hs, add_sub_cancel_left, mul_div_cancel_left₀ _ hs.ne',
      Real.sigmoid_log_div_one_sub hu.1 hu.2]
  have hmono : StrictMono (cdf (logisticMeasure m s)) := fun x y hxy => by
    rw [cdf_logisticMeasure_eq hs, cdf_logisticMeasure_eq hs]
    exact Real.sigmoid_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right hxy m) hs)
  have hq := Measure.quantile_cdf (logisticMeasure m s) (hmono.strictMonoOn _)
    (x := m + s * Real.log (u / (1 - u))) (by rw [hcdf]; exact hu)
  rwa [hcdf] at hq

/-! ### Affine transport and parameter measurability -/

/-- **Affine transport of the logistic law.** For `b ≠ 0`, the image of the logistic law with
location `m` and scale `s` under `x ↦ a + b * x` is the logistic law with location `a + b * m` and
scale `|b| * s`. A negative slope is absorbed by the symmetry of the logistic law about its
location. -/
theorem map_affine_logisticMeasure (m s : ℝ) {a b : ℝ} (hb : b ≠ 0) :
    (logisticMeasure m s).map (fun x => a + b * x) = logisticMeasure (a + b * m) (|b| * s) := by
  rw [logisticMeasure_eq_withDensity, map_affine_withDensity_volume _ hb,
    logisticMeasure_eq_withDensity]
  congr 1
  funext x
  rw [affineDensity_apply, logisticPDF, logisticPDF, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases le_or_gt s 0 with hs | hs
  · rw [logisticPDFReal_of_nonpos hs, logisticPDFReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg b) hs), mul_zero]
  have hbs : 0 < |b| * s := mul_pos (abs_pos.mpr hb) hs
  rw [logisticPDFReal_eq_sigmoid hs, logisticPDFReal_eq_sigmoid hbs]
  rcases lt_or_gt_of_ne hb with hb' | hb'
  · -- At a negative slope the standardized point changes sign, and `σ (1 - σ)` is even.
    have hy : ((x - a) / b - m) / s = -((x - (a + b * m)) / (|b| * s)) := by
      rw [abs_of_neg hb']
      field_simp
      ring
    rw [hy, Real.sigmoid_neg, sub_sub_cancel, abs_of_neg hb']
    field_simp
  · have hy : ((x - a) / b - m) / s = (x - (a + b * m)) / (|b| * s) := by
      rw [abs_of_pos hb']
      field_simp
      ring
    rw [hy, abs_of_pos hb']
    field_simp

/-- **The logistic family is measurable in its parameters**, so it can be packaged as a
kernel. -/
@[fun_prop]
theorem measurable_logisticMeasure : Measurable fun p : ℝ × ℝ => logisticMeasure p.1 p.2 := by
  simp only [logisticMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_logisticPDF

end Probability

end TauCeti
