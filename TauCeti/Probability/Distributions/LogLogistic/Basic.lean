/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Logistic.Basic
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The log-logistic distribution

The log-logistic law with scale `a > 0` and shape `b > 0` is the law of `exp Y` for a logistic
variable `Y` with location `log a` and scale `b⁻¹`, and it is *defined* here as that pushforward
of `logisticMeasure (Real.log a) b⁻¹`. Its cumulative distribution function on the positive
half-line is `(1 + (x / a) ^ (-b))⁻¹`, and its density there is
`(b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) ^ 2`. It is the law of a positive quantity
whose logarithm is logistic, in the same way as the log-normal law is the law of a positive
quantity whose logarithm is Gaussian.

**Boundary.** Unless both parameters are positive there is no log-logistic law:
`logLogisticMeasure a b` and its density are *defined* to vanish there
(`logLogisticMeasure_of_not_pos`, `logLogisticPDFReal_of_not_pos`). The density presentation
`logLogisticMeasure_eq_withDensity` and the scaling identity `map_mul_logLogisticMeasure` hold at
every parameter, which is what makes the family measurable in its parameters with no case split.

## Main definitions

* `TauCeti.Probability.logLogisticMeasure` — the law, as the image of a logistic law under
  `Real.exp`;
* `TauCeti.Probability.logLogisticPDFReal` and `TauCeti.Probability.logLogisticPDF` — its density
  against Lebesgue measure, in real- and `ℝ≥0∞`-valued form.

## Main results

* `isProbabilityMeasure_logLogisticMeasure` — it is a probability measure for positive
  parameters;
* `hasLaw_logLogisticMeasure_of_hasLaw_logisticMeasure` and `map_log_logLogisticMeasure` — the
  exponential of a logistic variable is log-logistic, and conversely its logarithm is logistic;
* `logLogisticMeasure_eq_withDensity`, `hasPDF_of_hasLaw_logLogisticMeasure`,
  `pdf_eq_logLogisticPDF_of_hasLaw_logLogisticMeasure` and `rnDeriv_logLogisticMeasure` — the
  density;
* `support_logLogisticMeasure` — the topological support is the closed half-line `Ici 0`;
* `cdf_logLogisticMeasure_eq` — the cdf;
* `one_sub_cdf_logLogisticMeasure`, `logLogisticPDFReal_div_one_sub_cdf` and
  `neg_log_one_sub_cdf_logLogisticMeasure` — the survival function `(1 + (x / a) ^ b)⁻¹`, the
  hazard rate and the cumulative hazard `log (1 + (x / a) ^ b)`;
* `map_mul_logLogisticMeasure` — multiplying by `c > 0` multiplies the scale by `c`;
* `measurable_logLogisticMeasure` — the family is measurable in its two parameters.

## Implementation

Everything except the density is read off the logistic law through the pushforward: the cdf is
the logistic cdf at `log x`, since `exp ⁻¹' Iic x = Iic (log x)` for `0 < x`, and the scaling
identity is the logistic translation by `log c`. The density is the one change of variables:
`Real.exp` is injective with derivative `exp` and image `Ioi 0`, so
`TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul` carries the logistic density to
`logLogisticPDF` on `Ioi 0`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 23.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {a b c x : ℝ}

/-! ### The law -/

/-- The log-logistic law with scale `a` and shape `b`: the law of `exp Y` when `Y` is logistic
with location `log a` and scale `b⁻¹`.

Unless `0 < a` and `0 < b` this is the zero measure, not a probability measure; see
`logLogisticMeasure_of_not_pos`. -/
def logLogisticMeasure (a b : ℝ) : Measure ℝ :=
  if 0 < a ∧ 0 < b then (logisticMeasure (Real.log a) b⁻¹).map Real.exp else 0

/-- For positive parameters the log-logistic law is the image of a logistic law under
`Real.exp`. -/
theorem logLogisticMeasure_of_pos (ha : 0 < a) (hb : 0 < b) :
    logLogisticMeasure a b = (logisticMeasure (Real.log a) b⁻¹).map Real.exp := by
  rw [logLogisticMeasure, ite_eq_left ⟨ha, hb⟩]

/-- Outside the valid parameter range the log-logistic law is the zero measure. -/
@[simp]
theorem logLogisticMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) : logLogisticMeasure a b = 0 := by
  rw [logLogisticMeasure, ite_eq_right h]

/-- For positive parameters the log-logistic law is a probability measure. -/
theorem isProbabilityMeasure_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (logLogisticMeasure a b) := by
  have := isProbabilityMeasure_logisticMeasure (inv_pos.mpr hb) (Real.log a)
  rw [logLogisticMeasure_of_pos ha hb]
  infer_instance

/-- The log-logistic law is a probability measure exactly at positive parameters. -/
@[simp]
theorem isProbabilityMeasure_logLogisticMeasure_iff :
    IsProbabilityMeasure (logLogisticMeasure a b) ↔ 0 < a ∧ 0 < b := by
  refine ⟨fun h => ?_, fun h => isProbabilityMeasure_logLogisticMeasure h.1 h.2⟩
  by_contra hab
  rw [logLogisticMeasure_of_not_pos hab] at h
  exact not_isProbabilityMeasure_zero h

/-- **The log-logistic law from a logistic variable.** If `Y` is logistic with location `log a`
and scale `b⁻¹`, then `exp Y` has the log-logistic law with scale `a` and shape `b`. -/
theorem hasLaw_logLogisticMeasure_of_hasLaw_logisticMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℝ} (ha : 0 < a) (hb : 0 < b)
    (hY : HasLaw Y (logisticMeasure (Real.log a) b⁻¹) P) :
    HasLaw (fun ω => Real.exp (Y ω)) (logLogisticMeasure a b) P := by
  rw [logLogisticMeasure_of_pos ha hb]
  exact (hasLaw_map Real.measurable_exp.aemeasurable).comp hY

/-- **The logarithm of a log-logistic variable is logistic**, with location `log a` and scale
`b⁻¹`. -/
theorem map_log_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) :
    (logLogisticMeasure a b).map Real.log = logisticMeasure (Real.log a) b⁻¹ := by
  rw [logLogisticMeasure_of_pos ha hb,
    Measure.map_map Real.measurable_log Real.measurable_exp]
  simp only [Function.comp_def, Real.log_exp, Measure.map_id']

/-- A log-logistic variable is almost surely positive, including vacuously at invalid
parameters. -/
theorem ae_mem_Ioi_logLogisticMeasure (a b : ℝ) : ∀ᵐ x ∂logLogisticMeasure a b, x ∈ Ioi 0 := by
  by_cases h : 0 < a ∧ 0 < b
  · rw [logLogisticMeasure_of_pos h.1 h.2]
    exact (ae_map_iff Real.measurable_exp.aemeasurable measurableSet_Ioi).mpr
      (ae_of_all _ Real.exp_pos)
  · rw [logLogisticMeasure_of_not_pos h]
    simp

/-- The log-logistic law gives no mass to the nonpositive half-line. -/
@[simp]
theorem logLogisticMeasure_Iic_zero (a b : ℝ) : logLogisticMeasure a b (Iic 0) = 0 :=
  measure_mono_null (fun _ hy => not_lt.mpr (mem_Iic.mp hy))
    (ae_iff.mp (ae_mem_Ioi_logLogisticMeasure a b))

/-! ### The density -/

/-- The density of the log-logistic law with scale `a` and shape `b`, as a real-valued function:
`(b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) ^ 2` on the positive half-line, and `0`
elsewhere.

Unless `0 < a` and `0 < b` there is no such law and the density is `0`. -/
def logLogisticPDFReal (a b x : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b ∧ 0 < x then (b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) ^ 2 else 0

/-- The density of the log-logistic law, as a function valued in `ℝ≥0∞`. -/
def logLogisticPDF (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logLogisticPDFReal a b x)

/-- The `ℝ≥0∞`-valued log-logistic density is the coercion of the real-valued one. -/
theorem logLogisticPDF_eq_ofReal (a b x : ℝ) :
    logLogisticPDF a b x = ENNReal.ofReal (logLogisticPDFReal a b x) := (rfl)

/-- For positive parameters and a positive point the log-logistic density is
`(b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) ^ 2`. -/
@[simp]
theorem logLogisticPDFReal_of_pos (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    logLogisticPDFReal a b x = (b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) ^ 2 := by
  rw [logLogisticPDFReal, ite_eq_left ⟨ha, hb, hx⟩]

/-- The log-logistic density vanishes on the nonpositive half-line. -/
@[simp]
theorem logLogisticPDFReal_of_nonpos (hx : x ≤ 0) (a b : ℝ) : logLogisticPDFReal a b x = 0 := by
  rw [logLogisticPDFReal, ite_eq_right fun h => hx.not_gt h.2.2]

/-- Outside the valid parameter range the log-logistic density vanishes. -/
@[simp]
theorem logLogisticPDFReal_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) (x : ℝ) :
    logLogisticPDFReal a b x = 0 := by
  rw [logLogisticPDFReal, ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]

/-- The log-logistic density is strictly positive on the positive half-line. -/
theorem logLogisticPDFReal_pos (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    0 < logLogisticPDFReal a b x := by
  rw [logLogisticPDFReal_of_pos ha hb hx]
  have : 0 < x / a := div_pos hx ha
  positivity

/-- The log-logistic density is nonnegative at every parameter, valid or not. -/
theorem logLogisticPDFReal_nonneg (a b x : ℝ) : 0 ≤ logLogisticPDFReal a b x := by
  by_cases h : 0 < a ∧ 0 < b ∧ 0 < x
  · exact (logLogisticPDFReal_pos h.1 h.2.1 h.2.2).le
  · rw [logLogisticPDFReal, ite_eq_right h]

/-- The two log-logistic densities agree under `ENNReal.toReal`; the density is never
infinite. -/
@[simp]
theorem toReal_logLogisticPDF (a b x : ℝ) :
    (logLogisticPDF a b x).toReal = logLogisticPDFReal a b x :=
  ENNReal.toReal_ofReal (logLogisticPDFReal_nonneg a b x)

/-- The log-logistic density is measurable jointly in its scale, its shape and the point. -/
@[fun_prop]
theorem measurable_uncurry_logLogisticPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ => logLogisticPDFReal q.1.1 q.1.2 q.2 := by
  simp only [logLogisticPDFReal]
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_fst.fst).inter
    ((measurableSet_lt measurable_const measurable_fst.snd).inter
      (measurableSet_lt measurable_const measurable_snd))

/-- The `ℝ≥0∞`-valued log-logistic density is measurable jointly in its parameters and the
point. -/
@[fun_prop]
theorem measurable_uncurry_logLogisticPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => logLogisticPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_logLogisticPDFReal.ennreal_ofReal

/-- The real-valued log-logistic density is measurable. -/
@[fun_prop]
theorem measurable_logLogisticPDFReal (a b : ℝ) : Measurable (logLogisticPDFReal a b) :=
  measurable_uncurry_logLogisticPDFReal.comp (measurable_prodMk_left (x := (a, b)))

/-- The `ℝ≥0∞`-valued log-logistic density is measurable. -/
@[fun_prop]
theorem measurable_logLogisticPDF (a b : ℝ) : Measurable (logLogisticPDF a b) :=
  (measurable_logLogisticPDFReal a b).ennreal_ofReal

/-- For positive parameters, the function support of the log-logistic density is the positive
half-line. -/
@[simp]
theorem support_logLogisticPDF (ha : 0 < a) (hb : 0 < b) :
    Function.support (logLogisticPDF a b) = Ioi 0 := by
  ext x
  rw [Function.mem_support, mem_Ioi, logLogisticPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact ⟨fun h => lt_of_not_ge fun hx => h.ne' (logLogisticPDFReal_of_nonpos hx a b),
    logLogisticPDFReal_pos ha hb⟩

/-- The Jacobian identity behind the change of variables: the logistic density at `y` is the
log-logistic density at `exp y` weighted by the derivative of `exp`. -/
private lemma ofReal_abs_exp_mul_logLogisticPDF (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    ENNReal.ofReal |Real.exp y| * logLogisticPDF a b (Real.exp y) =
      logisticPDF (Real.log a) b⁻¹ y := by
  rw [abs_of_pos (Real.exp_pos y), logLogisticPDF, logisticPDF_eq_ofReal,
    ← ENNReal.ofReal_mul (Real.exp_nonneg y), logLogisticPDFReal_of_pos ha hb (Real.exp_pos y),
    logisticPDFReal_of_pos (inv_pos.mpr hb)]
  congr 1
  -- In the standardized coordinate `w = b * (y - log a)` both sides are `b eʷ / (1 + eʷ) ^ 2`.
  have hya : Real.exp y / a = Real.exp (y - Real.log a) := by
    rw [Real.exp_sub, Real.exp_log ha]
  have hw : (y - Real.log a) / b⁻¹ = (y - Real.log a) * b := by
    rw [div_inv_eq_mul]
  rw [hya, ← Real.exp_mul, ← Real.exp_mul, hw, Real.exp_neg]
  have hE : Real.exp ((y - Real.log a) * (b - 1)) * Real.exp (y - Real.log a) =
      Real.exp ((y - Real.log a) * b) := by
    rw [← Real.exp_add]
    ring_nf
  have hexp_y : Real.exp y = a * Real.exp (y - Real.log a) := by
    rw [Real.exp_sub, Real.exp_log ha]
    field_simp
  rw [hexp_y, ← hE]
  have h1 := Real.exp_pos (y - Real.log a)
  have h2 := Real.exp_pos ((y - Real.log a) * (b - 1))
  field_simp
  ring

/-- **The density of the log-logistic law.** The log-logistic law is
`volume.withDensity logLogisticPDF`, at every parameter: outside the valid range both sides are
zero. -/
theorem logLogisticMeasure_eq_withDensity (a b : ℝ) :
    logLogisticMeasure a b = volume.withDensity (logLogisticPDF a b) := by
  by_cases h : 0 < a ∧ 0 < b
  · have hmap := MeasureTheory.map_withDensity_abs_deriv_mul (f := logLogisticPDF a b)
      MeasurableSet.univ Real.measurable_exp (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
      Real.exp_injective.injOn
    simp only [Measure.restrict_univ, ofReal_abs_exp_mul_logLogisticPDF h.1 h.2, image_univ,
      Real.range_exp] at hmap
    have hind : (Ioi (0 : ℝ)).indicator (logLogisticPDF a b) = logLogisticPDF a b :=
      indicator_eq_self.mpr (support_logLogisticPDF h.1 h.2).le
    rw [logLogisticMeasure_of_pos h.1 h.2, logisticMeasure_eq_withDensity, hmap,
      ← withDensity_indicator measurableSet_Ioi, hind]
  · have hpdf : logLogisticPDF a b = 0 := funext fun x => by
      rw [logLogisticPDF, logLogisticPDFReal_of_not_pos h, ENNReal.ofReal_zero, Pi.zero_apply]
    rw [logLogisticMeasure_of_not_pos h, hpdf, withDensity_zero]

section DensityCorollaries

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a log-logistic law has a density. -/
theorem hasPDF_of_hasLaw_logLogisticMeasure (hX : HasLaw X (logLogisticMeasure a b) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_logLogisticPDF a b).aemeasurable
    (by rwa [logLogisticMeasure_eq_withDensity] at hX)

/-- The density of a log-logistic law is `logLogisticPDF`. -/
theorem pdf_eq_logLogisticPDF_of_hasLaw_logLogisticMeasure
    (hX : HasLaw X (logLogisticMeasure a b) P) :
    pdf X P volume =ᵐ[volume] logLogisticPDF a b :=
  pdf_eq_of_hasLaw_withDensity (measurable_logLogisticPDF a b).aemeasurable
    (by rwa [logLogisticMeasure_eq_withDensity] at hX)

end DensityCorollaries

/-- The Radon–Nikodym derivative of a log-logistic law against Lebesgue measure is
`logLogisticPDF`. -/
theorem rnDeriv_logLogisticMeasure (a b : ℝ) :
    (logLogisticMeasure a b).rnDeriv volume =ᵐ[volume] logLogisticPDF a b := by
  rw [logLogisticMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_logLogisticPDF a b)

/-! ### Topological support -/

/-- **The topological support of a log-logistic law** is the closed nonnegative half-line.
Although the law is almost surely strictly positive, every neighborhood of zero has positive
mass. -/
@[simp]
theorem support_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) :
    (logLogisticMeasure a b).support = Ici 0 := by
  rw [logLogisticMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_logLogisticPDF a b) isOpen_Ioi
      (support_logLogisticPDF ha hb), closure_Ioi]

/-! ### The cumulative distribution function -/

/-- **The cdf of the log-logistic law** is `0` on the nonpositive half-line and
`(1 + (x / a) ^ (-b))⁻¹` on the positive half-line. -/
theorem cdf_logLogisticMeasure_eq (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    cdf (logLogisticMeasure a b) x = if x ≤ 0 then 0 else (1 + (x / a) ^ (-b))⁻¹ := by
  have := isProbabilityMeasure_logisticMeasure (inv_pos.mpr hb) (Real.log a)
  have := isProbabilityMeasure_logLogisticMeasure ha hb
  rw [cdf_eq_real, measureReal_def]
  split_ifs with hx
  · rw [measure_mono_null (Iic_subset_Iic.mpr hx) (logLogisticMeasure_Iic_zero a b),
      ENNReal.toReal_zero]
  · have hx' : 0 < x := lt_of_not_ge hx
    have hpre : Real.exp ⁻¹' Iic x = Iic (Real.log x) := by
      ext y
      simp [Real.le_log_iff_exp_le hx']
    rw [logLogisticMeasure_of_pos ha hb, Measure.map_apply Real.measurable_exp measurableSet_Iic,
      hpre, ← measureReal_def, ← cdf_eq_real, cdf_logisticMeasure_eq (inv_pos.mpr hb),
      Real.sigmoid_def, div_inv_eq_mul, ← Real.log_div hx'.ne' ha.ne',
      Real.rpow_def_of_pos (div_pos hx' ha)]
    ring_nf

/-! ### Survival and hazard -/

/-- **The survival function of the log-logistic law** is `(1 + (x / a) ^ b)⁻¹` on the
nonnegative half-line. -/
theorem one_sub_cdf_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) :
    1 - cdf (logLogisticMeasure a b) x = (1 + (x / a) ^ b)⁻¹ := by
  rw [cdf_logLogisticMeasure_eq ha hb]
  rcases hx.eq_or_lt with rfl | hx
  · simp [Real.zero_rpow hb.ne']
  · have hz := Real.rpow_pos_of_pos (div_pos hx ha) b
    rw [ite_eq_right hx.not_ge, Real.rpow_neg (div_pos hx ha).le]
    field_simp
    ring

/-- **The hazard rate of the log-logistic law**: on the positive half-line the density divided by
the survival function is `(b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b)`. -/
theorem logLogisticPDFReal_div_one_sub_cdf (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    logLogisticPDFReal a b x / (1 - cdf (logLogisticMeasure a b) x) =
      (b / a) * (x / a) ^ (b - 1) / (1 + (x / a) ^ b) := by
  have hz := Real.rpow_pos_of_pos (div_pos hx ha) b
  rw [one_sub_cdf_logLogisticMeasure ha hb hx.le, logLogisticPDFReal_of_pos ha hb hx]
  field_simp

/-- **The cumulative hazard of the log-logistic law** is `log (1 + (x / a) ^ b)` on the
nonnegative half-line. -/
theorem neg_log_one_sub_cdf_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) :
    -Real.log (1 - cdf (logLogisticMeasure a b) x) = Real.log (1 + (x / a) ^ b) := by
  rw [one_sub_cdf_logLogisticMeasure ha hb hx, Real.log_inv, neg_neg]

/-! ### Scaling and parameter measurability -/

/-- **Scaling of the log-logistic law.** Multiplication by `c > 0` multiplies the scale by `c` and
leaves the shape fixed. The identity also holds on the zero branch of invalid parameters. -/
theorem map_mul_logLogisticMeasure (hc : 0 < c) (a b : ℝ) :
    (logLogisticMeasure a b).map (c * ·) = logLogisticMeasure (c * a) b := by
  by_cases h : 0 < a ∧ 0 < b
  · have hexp : (c * ·) ∘ Real.exp = Real.exp ∘ fun y => Real.log c + 1 * y := by
      funext y
      simp only [Function.comp_apply, one_mul, Real.exp_add, Real.exp_log hc]
    rw [logLogisticMeasure_of_pos h.1 h.2, logLogisticMeasure_of_pos (mul_pos hc h.1) h.2,
      Measure.map_map (by fun_prop) Real.measurable_exp, hexp,
      ← Measure.map_map Real.measurable_exp (by fun_prop),
      map_affine_logisticMeasure _ _ one_ne_zero, one_mul, abs_one, one_mul,
      Real.log_mul hc.ne' h.1.ne']
  · have h' : ¬ (0 < c * a ∧ 0 < b) := fun h' =>
      h ⟨pos_of_mul_pos_right h'.1 hc.le, h'.2⟩
    rw [logLogisticMeasure_of_not_pos h, logLogisticMeasure_of_not_pos h', Measure.map_zero]

/-- The random-variable form of scaling: if `X` is log-logistic with scale `a` and shape `b`, then
`c * X` is log-logistic with scale `c * a` and shape `b` for `c > 0`. -/
theorem hasLaw_mul_logLogisticMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hc : 0 < c) (hX : HasLaw X (logLogisticMeasure a b) P) :
    HasLaw (fun ω => c * X ω) (logLogisticMeasure (c * a) b) P := by
  rw [← map_mul_logLogisticMeasure hc]
  exact (hasLaw_map (by fun_prop : Measurable (c * · : ℝ → ℝ)).aemeasurable).comp hX

/-- **The log-logistic family is measurable in its parameters**, so it can be packaged as a
kernel. -/
@[fun_prop]
theorem measurable_logLogisticMeasure :
    Measurable fun p : ℝ × ℝ => logLogisticMeasure p.1 p.2 := by
  simp only [logLogisticMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_logLogisticPDF

end TauCeti.Probability
