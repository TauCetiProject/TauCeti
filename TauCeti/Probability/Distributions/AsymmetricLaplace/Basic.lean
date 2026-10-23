/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Distributions.Laplace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Independence.Basic

/-!
# The asymmetric Laplace distribution

The asymmetric Laplace law with location `m`, left rate `l` and right rate `r` is the law of
`m + X - Y` for independent exponential variables `X` of rate `r` and `Y` of rate `l`. It glues
two exponential tails at `m`: its density is `l * r / (l + r) * exp (l * (x - m))` for `x ≤ m` and
`l * r / (l + r) * exp (-(r * (x - m)))` for `m < x`. Equal rates `l = r` give the Laplace law of
scale `r⁻¹`.

This file defines the law from the exponential construction, identifies it as the Lebesgue measure
weighted by the glued density, and computes its cdf, characteristic function, mean and variance.

**Boundary.** Both rates must be positive. For `l ≤ 0` or `r ≤ 0` the measure and both densities
are *defined* to vanish (`asymmetricLaplaceMeasure_of_nonpos_left`,
`asymmetricLaplaceMeasure_of_nonpos_right`); formulas describing the probability law carry
`0 < l` and `0 < r` as hypotheses.

## Main definitions

* `TauCeti.Probability.asymmetricLaplacePDFReal` — the real-valued density;
* `TauCeti.Probability.asymmetricLaplacePDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.asymmetricLaplaceMeasure` — the law, as the pushforward of a product of two
  exponential laws under `(x, y) ↦ m + x - y`.

## Main results

* `isProbabilityMeasure_asymmetricLaplaceMeasure` — it is a probability measure for positive rates;
* `ProbabilityTheory.IndepFun.hasLaw_asymmetricLaplaceMeasure` — `m + X - Y` has this law
  for independent exponential variables `X` and `Y`;
* `charFun_asymmetricLaplaceMeasure` — the characteristic function
  `exp (i m t) * r * l / ((r - i t) * (l + i t))`;
* `asymmetricLaplaceMeasure_eq_withDensity` — the law is Lebesgue measure weighted by
  `asymmetricLaplacePDF`, for every choice of parameters;
* `hasPDF_of_hasLaw_asymmetricLaplaceMeasure`,
  `pdf_eq_asymmetricLaplacePDF_of_hasLaw_asymmetricLaplaceMeasure` and
  `rnDeriv_asymmetricLaplaceMeasure` — the density API;
* `cdf_asymmetricLaplaceMeasure_eq` — the cdf is `r / (l + r) * exp (l * (x - m))` up to the
  location and `1 - l / (l + r) * exp (-(r * (x - m)))` above it;
* `memLp_id_asymmetricLaplaceMeasure` and `integrable_id_asymmetricLaplaceMeasure` — the identity
  is square-integrable, hence integrable;
* `integral_id_asymmetricLaplaceMeasure` and `variance_id_asymmetricLaplaceMeasure` — the mean
  `m + r⁻¹ - l⁻¹` and the variance `(r ^ 2)⁻¹ + (l ^ 2)⁻¹`;
* `asymmetricLaplaceMeasure_self` — equal rates give the Laplace law of scale `r⁻¹`;
* `measurable_asymmetricLaplaceMeasure` — the family is measurable in its three parameters.

## Implementation

The density is identified through characteristic functions. On the construction side the integrand
`exp (i t (m + x - y))` factors over the product measure, so `charFun_expMeasure` gives the
transform at once. On the density side each half-line integral is a complex exponential integral,
evaluated by `integral_exp_mul_complex_Iic` and `integral_exp_mul_complex_Ioi`. The mean and
variance are read off the construction rather than integrated against the density.

## References

* S. Kotz, T. J. Kozubowski, K. Podgórski, *The Laplace Distribution and Generalizations*,
  Birkhäuser (2001), ch. 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m l r x : ℝ}

/-! ### The density -/

/-- The density of the asymmetric Laplace law with location `m`, left rate `l` and right rate
`r`, as a real-valued function.

If `l ≤ 0` or `r ≤ 0` there is no such law and the density is `0`. -/
def asymmetricLaplacePDFReal (m l r x : ℝ) : ℝ :=
  if 0 < l ∧ 0 < r then
    if x ≤ m then l * r / (l + r) * Real.exp (l * (x - m))
    else l * r / (l + r) * Real.exp (-(r * (x - m)))
  else 0

/-- The density of the asymmetric Laplace law, as a function valued in `ℝ≥0∞`. -/
def asymmetricLaplacePDF (m l r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (asymmetricLaplacePDFReal m l r x)

/-- The `ℝ≥0∞`-valued asymmetric Laplace density is the coercion of the real-valued one. -/
theorem asymmetricLaplacePDF_eq_ofReal (m l r x : ℝ) :
    asymmetricLaplacePDF m l r x = ENNReal.ofReal (asymmetricLaplacePDFReal m l r x) := by
  rw [asymmetricLaplacePDF]

/-- For a nonpositive left rate the density vanishes. -/
@[simp]
theorem asymmetricLaplacePDFReal_of_nonpos_left (hl : l ≤ 0) (m r x : ℝ) :
    asymmetricLaplacePDFReal m l r x = 0 := by
  rw [asymmetricLaplacePDFReal, ite_eq_right fun h => (not_lt.mpr hl) h.1]

/-- For a nonpositive right rate the density vanishes. -/
@[simp]
theorem asymmetricLaplacePDFReal_of_nonpos_right (hr : r ≤ 0) (m l x : ℝ) :
    asymmetricLaplacePDFReal m l r x = 0 := by
  rw [asymmetricLaplacePDFReal, ite_eq_right fun h => (not_lt.mpr hr) h.2]

/-- At or below the location the density is the rising exponential branch. -/
@[simp]
theorem asymmetricLaplacePDFReal_of_le (hl : 0 < l) (hr : 0 < r) (hx : x ≤ m) :
    asymmetricLaplacePDFReal m l r x = l * r / (l + r) * Real.exp (l * (x - m)) := by
  rw [asymmetricLaplacePDFReal, ite_eq_left ⟨hl, hr⟩, ite_eq_left hx]

/-- Above the location the density is the decaying exponential branch. -/
@[simp]
theorem asymmetricLaplacePDFReal_of_lt (hl : 0 < l) (hr : 0 < r) (hx : m < x) :
    asymmetricLaplacePDFReal m l r x = l * r / (l + r) * Real.exp (-(r * (x - m))) := by
  rw [asymmetricLaplacePDFReal, ite_eq_left ⟨hl, hr⟩, ite_eq_right (not_le.mpr hx)]

/-- The asymmetric Laplace density is nonnegative at every parameter, valid or not. -/
theorem asymmetricLaplacePDFReal_nonneg (m l r x : ℝ) : 0 ≤ asymmetricLaplacePDFReal m l r x := by
  rw [asymmetricLaplacePDFReal]
  split_ifs with h
  · exact mul_nonneg (div_nonneg (mul_pos h.1 h.2).le (add_pos h.1 h.2).le) (Real.exp_pos _).le
  · exact mul_nonneg (div_nonneg (mul_pos h.1 h.2).le (add_pos h.1 h.2).le) (Real.exp_pos _).le
  · exact le_rfl

/-- For positive rates the asymmetric Laplace density is strictly positive everywhere. -/
theorem asymmetricLaplacePDFReal_pos (hl : 0 < l) (hr : 0 < r) (m x : ℝ) :
    0 < asymmetricLaplacePDFReal m l r x := by
  have hc : 0 < l * r / (l + r) := div_pos (mul_pos hl hr) (add_pos hl hr)
  rcases le_or_gt x m with hx | hx
  · rw [asymmetricLaplacePDFReal_of_le hl hr hx]
    exact mul_pos hc (Real.exp_pos _)
  · rw [asymmetricLaplacePDFReal_of_lt hl hr hx]
    exact mul_pos hc (Real.exp_pos _)

/-- The two asymmetric Laplace densities agree under `ENNReal.toReal`. -/
@[simp]
theorem toReal_asymmetricLaplacePDF (m l r x : ℝ) :
    (asymmetricLaplacePDF m l r x).toReal = asymmetricLaplacePDFReal m l r x :=
  ENNReal.toReal_ofReal (asymmetricLaplacePDFReal_nonneg m l r x)

/-- For a nonpositive left rate the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem asymmetricLaplacePDF_of_nonpos_left (hl : l ≤ 0) (m r x : ℝ) :
    asymmetricLaplacePDF m l r x = 0 := by
  rw [asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_of_nonpos_left hl,
    ENNReal.ofReal_zero]

/-- For a nonpositive right rate the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem asymmetricLaplacePDF_of_nonpos_right (hr : r ≤ 0) (m l x : ℝ) :
    asymmetricLaplacePDF m l r x = 0 := by
  rw [asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_of_nonpos_right hr,
    ENNReal.ofReal_zero]

/-- At or below the location the `ℝ≥0∞`-valued density is the rising exponential branch. -/
@[simp]
theorem asymmetricLaplacePDF_of_le (hl : 0 < l) (hr : 0 < r) (hx : x ≤ m) :
    asymmetricLaplacePDF m l r x =
      ENNReal.ofReal (l * r / (l + r) * Real.exp (l * (x - m))) := by
  rw [asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_of_le hl hr hx]

/-- Above the location the `ℝ≥0∞`-valued density is the decaying exponential branch. -/
@[simp]
theorem asymmetricLaplacePDF_of_lt (hl : 0 < l) (hr : 0 < r) (hx : m < x) :
    asymmetricLaplacePDF m l r x =
      ENNReal.ofReal (l * r / (l + r) * Real.exp (-(r * (x - m)))) := by
  rw [asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_of_lt hl hr hx]

/-- The real-valued asymmetric Laplace density is measurable. -/
@[fun_prop]
theorem measurable_asymmetricLaplacePDFReal (m l r : ℝ) :
    Measurable (asymmetricLaplacePDFReal m l r) := by
  unfold asymmetricLaplacePDFReal
  split_ifs
  · exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  · exact measurable_const

/-- The `ℝ≥0∞`-valued asymmetric Laplace density is measurable. -/
@[fun_prop]
theorem measurable_asymmetricLaplacePDF (m l r : ℝ) :
    Measurable (asymmetricLaplacePDF m l r) :=
  (measurable_asymmetricLaplacePDFReal m l r).ennreal_ofReal

/-! ### Mass of the two half-lines -/

/-- At or below the location the density is a constant multiple of `exp (l * y)`. -/
private lemma asymmetricLaplacePDFReal_eq_mul_exp_of_le (hl : 0 < l) (hr : 0 < r) {y : ℝ}
    (hy : y ≤ m) :
    asymmetricLaplacePDFReal m l r y =
      l * r / (l + r) * Real.exp (-(l * m)) * Real.exp (l * y) := by
  rw [asymmetricLaplacePDFReal_of_le hl hr hy, mul_assoc, ← Real.exp_add]
  ring_nf

/-- Above the location the density is a constant multiple of `exp (-r * y)`. -/
private lemma asymmetricLaplacePDFReal_eq_mul_exp_of_lt (hl : 0 < l) (hr : 0 < r) {y : ℝ}
    (hy : m < y) :
    asymmetricLaplacePDFReal m l r y =
      l * r / (l + r) * Real.exp (r * m) * Real.exp (-r * y) := by
  rw [asymmetricLaplacePDFReal_of_lt hl hr hy, mul_assoc, ← Real.exp_add]
  ring_nf

/-- The mass of the density below a point at or under the location. -/
theorem integral_asymmetricLaplacePDFReal_Iic (hl : 0 < l) (hr : 0 < r) (hx : x ≤ m) :
    ∫ y in Iic x, asymmetricLaplacePDFReal m l r y = r / (l + r) * Real.exp (l * (x - m)) := by
  rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => asymmetricLaplacePDFReal_eq_mul_exp_of_le hl hr (le_trans hy hx)),
    integral_const_mul, integral_exp_mul_Iic hl]
  have hx' : Real.exp (l * (x - m)) = Real.exp (-(l * m)) * Real.exp (l * x) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hx']
  field_simp

/-- The mass of the density above a point at or over the location. -/
theorem integral_asymmetricLaplacePDFReal_Ioi (hl : 0 < l) (hr : 0 < r) (hx : m ≤ x) :
    ∫ y in Ioi x, asymmetricLaplacePDFReal m l r y =
      l / (l + r) * Real.exp (-(r * (x - m))) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y (hy : x < y) =>
        asymmetricLaplacePDFReal_eq_mul_exp_of_lt hl hr (lt_of_le_of_lt hx hy)),
    integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hr)]
  have hx' : Real.exp (-(r * (x - m))) = Real.exp (r * m) * Real.exp (-r * x) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hx']
  field_simp

/-- The asymmetric Laplace density is integrable on the whole line for every parameter. -/
theorem integrable_asymmetricLaplacePDFReal (m l r : ℝ) :
    Integrable (asymmetricLaplacePDFReal m l r) := by
  by_cases hl : 0 < l
  · by_cases hr : 0 < r
    · rw [← integrableOn_univ, ← Iic_union_Ioi (a := m)]
      exact (IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic hl m).const_mul _)
          (fun y hy => (asymmetricLaplacePDFReal_eq_mul_exp_of_le hl hr hy).symm)
          measurableSet_Iic).union
        (IntegrableOn.congr_fun ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hr) m).const_mul _)
          (fun y hy => (asymmetricLaplacePDFReal_eq_mul_exp_of_lt hl hr hy).symm)
          measurableSet_Ioi)
    · simp [funext (asymmetricLaplacePDFReal_of_nonpos_right (not_lt.mp hr) m l)]
  · simp [funext (asymmetricLaplacePDFReal_of_nonpos_left (not_lt.mp hl) m r)]

/-- The asymmetric Laplace density is integrable on every lower half-line. -/
theorem integrableOn_asymmetricLaplacePDFReal_Iic :
    IntegrableOn (asymmetricLaplacePDFReal m l r) (Iic x) :=
  (integrable_asymmetricLaplacePDFReal m l r).integrableOn

/-- The asymmetric Laplace density is integrable on every upper half-line. -/
theorem integrableOn_asymmetricLaplacePDFReal_Ioi :
    IntegrableOn (asymmetricLaplacePDFReal m l r) (Ioi x) :=
  (integrable_asymmetricLaplacePDFReal m l r).integrableOn

/-- The asymmetric Laplace density integrates to `1`. -/
theorem integral_asymmetricLaplacePDFReal (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    ∫ y, asymmetricLaplacePDFReal m l r y = 1 := by
  rw [← integral_add_compl (s := Iic m) measurableSet_Iic
      (integrable_asymmetricLaplacePDFReal m l r),
    compl_Iic, integral_asymmetricLaplacePDFReal_Iic hl hr le_rfl,
    integral_asymmetricLaplacePDFReal_Ioi hl hr le_rfl]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- The `ℝ≥0∞`-valued asymmetric Laplace density has total mass `1`. -/
theorem lintegral_asymmetricLaplacePDF_eq_one (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    ∫⁻ y, asymmetricLaplacePDF m l r y = 1 := by
  simp_rw [asymmetricLaplacePDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_asymmetricLaplacePDFReal m l r)
      (ae_of_all _ fun y => asymmetricLaplacePDFReal_nonneg m l r y),
    integral_asymmetricLaplacePDFReal hl hr m, ENNReal.ofReal_one]

/-! ### The measure -/

/-- The asymmetric Laplace law with location `m`, left rate `l` and right rate `r`: the law of
`m + X - Y` for independent exponential variables `X` of rate `r` and `Y` of rate `l`.

If `l ≤ 0` or `r ≤ 0` this is the zero measure, not a probability measure; see
`asymmetricLaplaceMeasure_of_nonpos_left` and `asymmetricLaplaceMeasure_of_nonpos_right`. -/
def asymmetricLaplaceMeasure (m l r : ℝ) : Measure ℝ :=
  if 0 < l ∧ 0 < r then
    ((expMeasure r).prod (expMeasure l)).map fun z => m + z.1 - z.2
  else 0

/-- For positive rates the asymmetric Laplace law is the pushforward of a product of exponential
laws under `(x, y) ↦ m + x - y`. -/
theorem asymmetricLaplaceMeasure_of_pos (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    asymmetricLaplaceMeasure m l r =
      ((expMeasure r).prod (expMeasure l)).map fun z => m + z.1 - z.2 := by
  rw [asymmetricLaplaceMeasure, ite_eq_left ⟨hl, hr⟩]

/-- For a nonpositive left rate the asymmetric Laplace law is the zero measure. -/
@[simp]
theorem asymmetricLaplaceMeasure_of_nonpos_left (hl : l ≤ 0) (m r : ℝ) :
    asymmetricLaplaceMeasure m l r = 0 := by
  rw [asymmetricLaplaceMeasure, ite_eq_right fun h => (not_lt.mpr hl) h.1]

/-- For a nonpositive right rate the asymmetric Laplace law is the zero measure. -/
@[simp]
theorem asymmetricLaplaceMeasure_of_nonpos_right (hr : r ≤ 0) (m l : ℝ) :
    asymmetricLaplaceMeasure m l r = 0 := by
  rw [asymmetricLaplaceMeasure, ite_eq_right fun h => (not_lt.mpr hr) h.2]

/-- **For positive rates the asymmetric Laplace law is a probability measure.** -/
theorem isProbabilityMeasure_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    IsProbabilityMeasure (asymmetricLaplaceMeasure m l r) := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  rw [asymmetricLaplaceMeasure_of_pos hl hr]
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The characteristic function -/

/-- **The characteristic function of the asymmetric Laplace law**, read off the exponential
construction. -/
@[simp]
theorem charFun_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m t : ℝ) :
    charFun (asymmetricLaplaceMeasure m l r) t =
      Complex.exp (Complex.I * m * t) * (r * l) /
        ((r - Complex.I * t) * (l + Complex.I * t)) := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have hfactor : ∀ z : ℝ × ℝ, Complex.exp (t * ↑(m + z.1 - z.2) * Complex.I) =
      Complex.exp (Complex.I * m * t) *
        (Complex.exp (t * z.1 * Complex.I) * Complex.exp (↑(-t) * z.2 * Complex.I)) := by
    intro z
    rw [← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [asymmetricLaplaceMeasure_of_pos hl hr, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), funext hfactor, integral_const_mul,
    integral_prod_mul (fun x : ℝ => Complex.exp (t * x * Complex.I))
      (fun y : ℝ => Complex.exp (↑(-t) * y * Complex.I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_expMeasure hr, charFun_expMeasure hl]
  have hden : (l : ℂ) + Complex.I * t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hl)
  have hden' : (r : ℂ) - Complex.I * t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hr)
  push_cast
  rw [mul_neg, sub_neg_eq_add]
  field_simp

/-- The Fourier integral of the density over the lower half-line ending at the location. -/
private lemma integral_Iic_asymmetricLaplacePDFReal_smul_exp (hl : 0 < l) (hr : 0 < r)
    (m t : ℝ) :
    ∫ y in Iic m, asymmetricLaplacePDFReal m l r y • Complex.exp (t * y * Complex.I) =
      ((l * r / (l + r) : ℝ) : ℂ) * Complex.exp (Complex.I * m * t) / (l + Complex.I * t) := by
  have hre : 0 < ((l : ℂ) + t * Complex.I).re := by simpa using hl
  have hL : ∀ y ∈ Iic m, asymmetricLaplacePDFReal m l r y • Complex.exp (t * y * Complex.I) =
      ((l * r / (l + r) : ℝ) : ℂ) * Complex.exp (-(l * m)) *
        Complex.exp ((l + t * Complex.I) * y) := fun y hy => by
    have h : Complex.exp ((l * (y - m) : ℝ) : ℂ) * Complex.exp (t * y * Complex.I) =
        Complex.exp (-(l * m)) * Complex.exp ((l + t * Complex.I) * y) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [asymmetricLaplacePDFReal_of_le hl hr hy, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_exp]
    linear_combination ((l * r / (l + r) : ℝ) : ℂ) * h
  have hexp : Complex.exp (-(l * m)) * Complex.exp (((l : ℂ) + t * Complex.I) * m) =
      Complex.exp (Complex.I * m * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Iic hL, integral_const_mul,
    integral_exp_mul_complex_Iic hre, ← hexp]
  ring

/-- The Fourier integral of the density over the upper half-line starting at the location. -/
private lemma integral_Ioi_asymmetricLaplacePDFReal_smul_exp (hl : 0 < l) (hr : 0 < r)
    (m t : ℝ) :
    ∫ y in Ioi m, asymmetricLaplacePDFReal m l r y • Complex.exp (t * y * Complex.I) =
      ((l * r / (l + r) : ℝ) : ℂ) * Complex.exp (Complex.I * m * t) / (r - Complex.I * t) := by
  have hre : ((-r : ℂ) + t * Complex.I).re < 0 := by simpa using hr
  have hR : ∀ y ∈ Ioi m, asymmetricLaplacePDFReal m l r y • Complex.exp (t * y * Complex.I) =
      ((l * r / (l + r) : ℝ) : ℂ) * Complex.exp (r * m) *
        Complex.exp ((-r + t * Complex.I) * y) := fun y (hy : m < y) => by
    have h : Complex.exp ((-(r * (y - m)) : ℝ) : ℂ) * Complex.exp (t * y * Complex.I) =
        Complex.exp (r * m) * Complex.exp ((-r + t * Complex.I) * y) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [asymmetricLaplacePDFReal_of_lt hl hr hy, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_exp]
    linear_combination ((l * r / (l + r) : ℝ) : ℂ) * h
  have hexp : Complex.exp (r * m) * Complex.exp ((-(r : ℂ) + t * Complex.I) * m) =
      Complex.exp (Complex.I * m * t) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hden : (-r : ℂ) + t * Complex.I ≠ 0 := fun h => by simp [h] at hre
  have hden' : (r : ℂ) - t * Complex.I ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hr)
  rw [setIntegral_congr_fun measurableSet_Ioi hR, integral_const_mul,
    integral_exp_mul_complex_Ioi hre, ← hexp]
  field_simp
  ring

/-- The characteristic function of Lebesgue measure weighted by the asymmetric Laplace density. -/
private lemma charFun_withDensity_asymmetricLaplacePDF (hl : 0 < l) (hr : 0 < r) (m t : ℝ) :
    charFun (volume.withDensity (asymmetricLaplacePDF m l r)) t =
      Complex.exp (Complex.I * m * t) * (r * l) /
        ((r - Complex.I * t) * (l + Complex.I * t)) := by
  have hint : Integrable
      (fun y : ℝ => asymmetricLaplacePDFReal m l r y • Complex.exp (t * y * Complex.I)) :=
    (integrable_asymmetricLaplacePDFReal m l r).smul_of_top_left
      (memLp_top_of_bound (by fun_prop) 1 (ae_of_all _ fun y => by
        rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]))
  rw [charFun_apply_real, funext (asymmetricLaplacePDF_eq_ofReal m l r),
    integral_withDensity_ofReal (measurable_asymmetricLaplacePDFReal m l r).aemeasurable
      (ae_of_all _ (asymmetricLaplacePDFReal_nonneg m l r)),
    ← integral_add_compl (s := Iic m) measurableSet_Iic hint, compl_Iic,
    integral_Iic_asymmetricLaplacePDFReal_smul_exp hl hr,
    integral_Ioi_asymmetricLaplacePDFReal_smul_exp hl hr]
  have hden : (l : ℂ) + Complex.I * t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hl)
  have hden' : (r : ℂ) - Complex.I * t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hr)
  have hsum : (l : ℂ) + r ≠ 0 := by exact_mod_cast (add_pos hl hr).ne'
  push_cast
  field_simp
  ring

/-- **The asymmetric Laplace law has the glued exponential density.** This holds for every
choice of parameters: for a nonpositive rate both sides are the zero measure. -/
theorem asymmetricLaplaceMeasure_eq_withDensity (m l r : ℝ) :
    asymmetricLaplaceMeasure m l r = volume.withDensity (asymmetricLaplacePDF m l r) := by
  by_cases hl : 0 < l
  · by_cases hr : 0 < r
    · have := isProbabilityMeasure_asymmetricLaplaceMeasure hl hr m
      have : IsProbabilityMeasure (volume.withDensity (asymmetricLaplacePDF m l r)) := ⟨by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          lintegral_asymmetricLaplacePDF_eq_one hl hr m]⟩
      refine Measure.ext_of_charFun (funext fun t => ?_)
      rw [charFun_asymmetricLaplaceMeasure hl hr, charFun_withDensity_asymmetricLaplacePDF hl hr]
    · have h : asymmetricLaplacePDF m l r = 0 :=
        funext (asymmetricLaplacePDF_of_nonpos_right (not_lt.mp hr) m l)
      rw [asymmetricLaplaceMeasure_of_nonpos_right (not_lt.mp hr), h, withDensity_zero]
  · have h : asymmetricLaplacePDF m l r = 0 :=
      funext (asymmetricLaplacePDF_of_nonpos_left (not_lt.mp hl) m r)
    rw [asymmetricLaplaceMeasure_of_nonpos_left (not_lt.mp hl), h, withDensity_zero]

/-! ### Transfer to the density -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against an asymmetric Laplace measure
exactly when its density-weighted version is Lebesgue integrable. -/
theorem integrable_asymmetricLaplaceMeasure_iff (m l r : ℝ) {g : ℝ → E} :
    Integrable g (asymmetricLaplaceMeasure m l r) ↔
      Integrable fun y ↦ asymmetricLaplacePDFReal m l r y • g y := by
  rw [asymmetricLaplaceMeasure_eq_withDensity, funext (asymmetricLaplacePDF_eq_ofReal m l r)]
  exact integrable_withDensity_ofReal_iff (measurable_asymmetricLaplacePDFReal m l r).aemeasurable
    (ae_of_all _ (asymmetricLaplacePDFReal_nonneg m l r))

/-- **Integral transfer.** An integral against an asymmetric Laplace measure is the
density-weighted Lebesgue integral. -/
theorem integral_asymmetricLaplaceMeasure_eq (m l r : ℝ) (g : ℝ → E) :
    ∫ y, g y ∂asymmetricLaplaceMeasure m l r = ∫ y, asymmetricLaplacePDFReal m l r y • g y := by
  rw [asymmetricLaplaceMeasure_eq_withDensity, funext (asymmetricLaplacePDF_eq_ofReal m l r)]
  exact integral_withDensity_ofReal (measurable_asymmetricLaplacePDFReal m l r).aemeasurable
    (ae_of_all _ (asymmetricLaplacePDFReal_nonneg m l r)) g

end Transfer

/-! ### Absolute continuity -/

variable {X : Ω → ℝ}

/-- A random variable with an asymmetric Laplace law has a density. -/
theorem hasPDF_of_hasLaw_asymmetricLaplaceMeasure
    (hX : HasLaw X (asymmetricLaplaceMeasure m l r) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_asymmetricLaplacePDF m l r).aemeasurable
    (asymmetricLaplaceMeasure_eq_withDensity m l r ▸ hX)

/-- The density of an asymmetric Laplace law is `asymmetricLaplacePDF`. -/
theorem pdf_eq_asymmetricLaplacePDF_of_hasLaw_asymmetricLaplaceMeasure
    (hX : HasLaw X (asymmetricLaplaceMeasure m l r) P) :
    pdf X P volume =ᵐ[volume] asymmetricLaplacePDF m l r :=
  pdf_eq_of_hasLaw_withDensity (measurable_asymmetricLaplacePDF m l r).aemeasurable
    (asymmetricLaplaceMeasure_eq_withDensity m l r ▸ hX)

/-- The Radon–Nikodym derivative of an asymmetric Laplace law against Lebesgue measure is
`asymmetricLaplacePDF`. -/
theorem rnDeriv_asymmetricLaplaceMeasure (m l r : ℝ) :
    (asymmetricLaplaceMeasure m l r).rnDeriv volume =ᵐ[volume] asymmetricLaplacePDF m l r := by
  rw [asymmetricLaplaceMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_asymmetricLaplacePDF m l r)

/-! ### The cumulative distribution function -/

/-- The mass an asymmetric Laplace law assigns to a measurable set, as a density integral. -/
private lemma measureReal_asymmetricLaplaceMeasure {s : Set ℝ} (hs : MeasurableSet s) :
    (asymmetricLaplaceMeasure m l r).real s = ∫ y in s, asymmetricLaplacePDFReal m l r y := by
  rw [asymmetricLaplaceMeasure_eq_withDensity, funext (asymmetricLaplacePDF_eq_ofReal m l r)]
  exact measureReal_withDensity_ofReal (ae_of_all _ (asymmetricLaplacePDFReal_nonneg m l r)) hs
    (integrable_asymmetricLaplacePDFReal m l r).integrableOn

/-- **The cumulative distribution function of the asymmetric Laplace law.** -/
theorem cdf_asymmetricLaplaceMeasure_eq (hl : 0 < l) (hr : 0 < r) (m x : ℝ) :
    cdf (asymmetricLaplaceMeasure m l r) x =
      if x ≤ m then r / (l + r) * Real.exp (l * (x - m))
      else 1 - l / (l + r) * Real.exp (-(r * (x - m))) := by
  have := isProbabilityMeasure_asymmetricLaplaceMeasure hl hr m
  rw [cdf_eq_real]
  split_ifs with hx
  · rw [measureReal_asymmetricLaplaceMeasure measurableSet_Iic,
      integral_asymmetricLaplacePDFReal_Iic hl hr hx]
  · rw [← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ,
      measureReal_asymmetricLaplaceMeasure measurableSet_Ioi,
      integral_asymmetricLaplacePDFReal_Ioi hl hr (not_le.mp hx).le]

/-! ### Mean and variance -/

/-- The identity is square-integrable against an asymmetric Laplace law, for all parameters. -/
theorem memLp_id_asymmetricLaplaceMeasure (m l r : ℝ) :
    MemLp id 2 (asymmetricLaplaceMeasure m l r) := by
  rcases le_or_gt l 0 with hl | hl
  · simp [asymmetricLaplaceMeasure_of_nonpos_left hl]
  rcases le_or_gt r 0 with hr | hr
  · simp [asymmetricLaplaceMeasure_of_nonpos_right hr]
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  rw [asymmetricLaplaceMeasure_of_pos hl hr, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact ((memLp_const m).add ((memLp_id_expMeasure hr).comp_measurePreserving
    measurePreserving_fst)).sub
    ((memLp_id_expMeasure hl).comp_measurePreserving measurePreserving_snd)

/-- The identity is integrable against an asymmetric Laplace law, for all parameters. -/
theorem integrable_id_asymmetricLaplaceMeasure (m l r : ℝ) :
    Integrable id (asymmetricLaplaceMeasure m l r) := by
  rcases le_or_gt l 0 with hl | hl
  · simp [asymmetricLaplaceMeasure_of_nonpos_left hl]
  rcases le_or_gt r 0 with hr | hr
  · simp [asymmetricLaplaceMeasure_of_nonpos_right hr]
  have := isProbabilityMeasure_asymmetricLaplaceMeasure hl hr m
  exact (memLp_id_asymmetricLaplaceMeasure m l r).integrable one_le_two

/-- **The mean of the asymmetric Laplace law** is `m + r⁻¹ - l⁻¹`. -/
theorem integral_id_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    ∫ x, x ∂asymmetricLaplaceMeasure m l r = m + r⁻¹ - l⁻¹ := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have hfst : Integrable (fun z : ℝ × ℝ => z.1) ((expMeasure r).prod (expMeasure l)) :=
    ((memLp_id_expMeasure hr).integrable one_le_two).comp_fst _
  have hsnd : Integrable (fun z : ℝ × ℝ => z.2) ((expMeasure r).prod (expMeasure l)) :=
    ((memLp_id_expMeasure hl).integrable one_le_two).comp_snd _
  rw [asymmetricLaplaceMeasure_of_pos hl hr, integral_map (by fun_prop) (by fun_prop),
    integral_sub (f := fun z : ℝ × ℝ => m + z.1) ((integrable_const m).add hfst) hsnd,
    integral_add (f := fun _ : ℝ × ℝ => m) (integrable_const m) hfst,
    integral_const]
  have h1 : ∫ z : ℝ × ℝ, z.1 ∂(expMeasure r).prod (expMeasure l) = r⁻¹ := by
    simpa [integral_id_expMeasure hr] using
      integral_fun_fst (μ := expMeasure r) (ν := expMeasure l) (fun x : ℝ => x)
  have h2 : ∫ z : ℝ × ℝ, z.2 ∂(expMeasure r).prod (expMeasure l) = l⁻¹ := by
    simpa [integral_id_expMeasure hl] using
      integral_fun_snd (μ := expMeasure r) (ν := expMeasure l) (fun x : ℝ => x)
  simp [h1, h2]

/-- **The variance of the asymmetric Laplace law** is `(r ^ 2)⁻¹ + (l ^ 2)⁻¹`, the sum of the
variances of its two exponential parts. -/
theorem variance_id_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m : ℝ) :
    Var[id; asymmetricLaplaceMeasure m l r] = (r ^ 2)⁻¹ + (l ^ 2)⁻¹ := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have hfst : MemLp (fun z : ℝ × ℝ => z.1) 2 ((expMeasure r).prod (expMeasure l)) :=
    (memLp_id_expMeasure hr).comp_measurePreserving measurePreserving_fst
  have hsnd : MemLp (fun z : ℝ × ℝ => -z.2) 2 ((expMeasure r).prod (expMeasure l)) :=
    ((memLp_id_expMeasure hl).comp_measurePreserving measurePreserving_snd).neg
  have hindep : (fun z : ℝ × ℝ => z.1) ⟂ᵢ[(expMeasure r).prod (expMeasure l)] fun z => -z.2 :=
    indepFun_prod measurable_id measurable_neg
  rw [asymmetricLaplaceMeasure_of_pos hl hr, variance_map aemeasurable_id (by fun_prop)]
  have hcomp : (id ∘ fun z : ℝ × ℝ => m + z.1 - z.2) = fun z => m + (z.1 + -z.2) := by
    funext z
    simp only [Function.comp_apply, id_eq]
    ring
  have hvfst : Var[fun z : ℝ × ℝ => z.1; (expMeasure r).prod (expMeasure l)] =
      Var[id; expMeasure r] :=
    (measurePreserving_fst (μ := expMeasure r) (ν := expMeasure l)).variance_fun_comp
      (f := id) aemeasurable_id
  have hvsnd : Var[fun z : ℝ × ℝ => z.2; (expMeasure r).prod (expMeasure l)] =
      Var[id; expMeasure l] :=
    (measurePreserving_snd (μ := expMeasure r) (ν := expMeasure l)).variance_fun_comp
      (f := id) aemeasurable_id
  rw [hcomp, variance_const_add (by fun_prop), hindep.variance_fun_add hfst hsnd,
    variance_fun_neg, hvfst, hvsnd, variance_id_expMeasure hr, variance_id_expMeasure hl]

/-! ### Equal rates -/

/-- **Equal rates give the Laplace law.** With both rates equal to `r`, the asymmetric Laplace law
is the Laplace law of scale `r⁻¹`. -/
@[simp]
theorem asymmetricLaplaceMeasure_self (m r : ℝ) :
    asymmetricLaplaceMeasure m r r = laplaceMeasure m r⁻¹ := by
  rw [asymmetricLaplaceMeasure_eq_withDensity, laplaceMeasure_eq_withDensity]
  congr 1
  funext x
  rw [asymmetricLaplacePDF_eq_ofReal, laplacePDF_eq_ofReal]
  congr 1
  rcases le_or_gt r 0 with hr | hr
  · rw [asymmetricLaplacePDFReal_of_nonpos_left hr,
      laplacePDFReal_of_nonpos (inv_nonpos.mpr hr)]
  rw [laplacePDFReal_of_pos (inv_pos.mpr hr), div_inv_eq_mul]
  have hc : r * r / (r + r) = (2 * r⁻¹)⁻¹ := by
    field_simp
    ring
  rcases le_or_gt x m with hx | hx
  · rw [asymmetricLaplacePDFReal_of_le hr hr hx, abs_of_nonpos (sub_nonpos.mpr hx), hc]
    ring_nf
  · rw [asymmetricLaplacePDFReal_of_lt hr hr hx, abs_of_pos (sub_pos.mpr hx), hc]
    ring_nf

/-! ### Measurability in the parameters -/

/-- The asymmetric Laplace density is measurable jointly in its three parameters and the point. -/
@[fun_prop]
theorem measurable_uncurry_asymmetricLaplacePDF :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => asymmetricLaplacePDF q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  simp only [asymmetricLaplacePDF, asymmetricLaplacePDFReal]
  refine (Measurable.ite ?_ (Measurable.ite ?_ ?_ ?_) measurable_const).ennreal_ofReal
  · exact (measurableSet_lt measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_const measurable_fst.snd.snd)
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

/-- **The asymmetric Laplace family is measurable in its parameters**, so it can be packaged as a
kernel. -/
@[fun_prop]
theorem measurable_asymmetricLaplaceMeasure :
    Measurable fun p : ℝ × ℝ × ℝ => asymmetricLaplaceMeasure p.1 p.2.1 p.2.2 := by
  simp_rw [asymmetricLaplaceMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_asymmetricLaplacePDF

end Probability

end TauCeti

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- **The exponential construction.** For independent exponential variables `X` of rate `r` and
`Y` of rate `l`, the variable `m + X - Y` has the asymmetric Laplace law with left rate `l` and
right rate `r`. -/
theorem hasLaw_asymmetricLaplaceMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {l r : ℝ} (hindep : IndepFun X Y P) (hl : 0 < l) (hr : 0 < r)
    (hX : HasLaw X (expMeasure r) P) (hY : HasLaw Y (expMeasure l) P) (m : ℝ) :
    HasLaw (fun ω => m + X ω - Y ω) (asymmetricLaplaceMeasure m l r) P := by
  have := isProbabilityMeasure_expMeasure hr
  have := hX.isProbabilityMeasure
  have hXY : HasLaw (fun ω => (X ω, Y ω)) ((expMeasure r).prod (expMeasure l)) P :=
    (indepFun_iff_hasLaw_prodMk_prod hX hY).1 hindep
  rw [asymmetricLaplaceMeasure_of_pos hl hr]
  exact (hasLaw_map (X := fun z : ℝ × ℝ => m + z.1 - z.2) (by fun_prop)).fun_comp hXY

end ProbabilityTheory.IndepFun
