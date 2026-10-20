/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Distributions.Uniform.Quantile
public import TauCeti.Probability.Quantile.Map
public import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The log-uniform distribution

The log-uniform law on positive endpoints `a < b` is the image of the uniform law on
`(log a, log b]` under the exponential map. Equivalently, its logarithm is uniform. This file
constructs the law and establishes its probability, carrier, cumulative distribution, quantile,
real-power moments, mean, variance, and exponential-integrability domain.

## Main results

* `TauCeti.Probability.logUniformMeasure` is the log-uniform law, totalized to zero unless
  `0 < a < b`;
* `TauCeti.Probability.logUniformMeasure_eq_withDensity` identifies its density and yields its
  topological support;
* `TauCeti.Probability.cdf_logUniformMeasure_eq` and
  `TauCeti.Probability.quantile_logUniformMeasure` give its cdf and interior quantile;
* `TauCeti.Probability.integral_rpow_logUniformMeasure` gives every real-power moment;
* `TauCeti.Probability.integrableExpSet_id_logUniformMeasure` shows that every exponential moment
  exists.

## Reference

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), section 15.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {a b q u x : ℝ}

/-! ### Definition and carrier -/

/-- The log-uniform measure with lower endpoint `a` and upper endpoint `b`.

For `0 < a < b`, this is the image of the uniform law on `(log a, log b]` under `exp`. For all
other parameters it is the zero measure. -/
def logUniformMeasure (a b : ℝ) : Measure ℝ :=
  if 0 < a ∧ a < b then (uniformMeasure (log a) (log b)).map exp else 0

/-- On valid endpoints, the log-uniform law is the exponential image of a uniform law. -/
theorem logUniformMeasure_of_pos (ha : 0 < a) (hab : a < b) :
    logUniformMeasure a b = (uniformMeasure (log a) (log b)).map exp := by
  rw [logUniformMeasure, ite_eq_left ⟨ha, hab⟩]

/-- Outside the valid parameter range the log-uniform law is zero. -/
@[simp]
theorem logUniformMeasure_of_not_pos (h : ¬ (0 < a ∧ a < b)) : logUniformMeasure a b = 0 := by
  rw [logUniformMeasure, ite_eq_right h]

/-- A log-uniform law with valid endpoints is a probability measure. -/
theorem isProbabilityMeasure_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    IsProbabilityMeasure (logUniformMeasure a b) := by
  rw [logUniformMeasure_of_pos ha hab]
  have hlog : log a < log b := strictMonoOn_log ha (ha.trans hab) hab
  have := isProbabilityMeasure_uniformMeasure hlog
  infer_instance

/-- A log-uniform variable lies in `(a, b]` almost surely. For invalid endpoints this holds
because the measure is zero. -/
theorem ae_mem_Ioc_logUniformMeasure (a b : ℝ) :
    ∀ᵐ y ∂logUniformMeasure a b, y ∈ Ioc a b := by
  by_cases h : 0 < a ∧ a < b
  · rw [logUniformMeasure_of_pos h.1 h.2]
    refine (ae_map_iff measurable_exp.aemeasurable measurableSet_Ioc).2 ?_
    filter_upwards [ae_mem_Ioc_uniformMeasure] with y hy
    constructor
    · simpa only [exp_log h.1] using Real.exp_lt_exp.mpr hy.1
    · simpa only [exp_log (h.1.trans h.2)] using Real.exp_le_exp.mpr hy.2
  · simp [logUniformMeasure_of_not_pos h]

/-- Taking logarithms recovers the defining uniform law. -/
theorem map_log_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    (logUniformMeasure a b).map log = uniformMeasure (log a) (log b) := by
  rw [logUniformMeasure_of_pos ha hab,
    Measure.map_map measurable_log measurable_exp]
  simp only [Function.comp_def, log_exp, Measure.map_id']

/-! ### Density and topological support -/

/-- The real density of the log-uniform law. It is `1 / (x * log (b / a))` on `(a, b)` for valid
endpoints, and zero elsewhere. -/
def logUniformPDFReal (a b x : ℝ) : ℝ :=
  if 0 < a ∧ a < b ∧ x ∈ Ioo a b then (x * log (b / a))⁻¹ else 0

/-- The `ENNReal`-valued density of the log-uniform law. -/
def logUniformPDF (a b x : ℝ) : ENNReal := ENNReal.ofReal (logUniformPDFReal a b x)

/-- The log-uniform density has its displayed value on the support interior. -/
@[simp]
theorem logUniformPDFReal_of_mem (ha : 0 < a) (hab : a < b) (hx : x ∈ Ioo a b) :
    logUniformPDFReal a b x = (x * log (b / a))⁻¹ := by
  rw [logUniformPDFReal, ite_eq_left ⟨ha, hab, hx⟩]

/-- The log-uniform density vanishes when the parameters or sample point are outside their valid
range. -/
@[simp]
theorem logUniformPDFReal_of_not (h : 0 < a → a < b → a < x → b ≤ x) :
    logUniformPDFReal a b x = 0 := by
  rw [logUniformPDFReal, ite_eq_right]
  exact fun hvalid ↦ (not_lt_of_ge (h hvalid.1 hvalid.2.1 hvalid.2.2.1)) hvalid.2.2.2

/-- The real log-uniform density is nonnegative. -/
theorem logUniformPDFReal_nonneg (a b x : ℝ) : 0 ≤ logUniformPDFReal a b x := by
  by_cases h : 0 < a ∧ a < b ∧ x ∈ Ioo a b
  · rw [logUniformPDFReal_of_mem h.1 h.2.1 h.2.2]
    exact inv_nonneg.mpr (mul_nonneg (h.1.trans h.2.2.1).le
      (log_pos ((one_lt_div h.1).2 h.2.1)).le)
  · rw [logUniformPDFReal_of_not]
    simpa only [Set.mem_Ioo, not_and, not_lt] using h

/-- The real log-uniform density is strictly positive on `(a, b)` for valid endpoints. -/
theorem logUniformPDFReal_pos (ha : 0 < a) (hab : a < b) (hx : x ∈ Ioo a b) :
    0 < logUniformPDFReal a b x := by
  rw [logUniformPDFReal_of_mem ha hab hx]
  exact inv_pos.mpr (mul_pos (ha.trans hx.1) (log_pos ((one_lt_div ha).2 hab)))

/-- For valid endpoints, the real log-uniform density is strictly positive exactly on
`(a, b)`. -/
theorem logUniformPDFReal_pos_iff (ha : 0 < a) (hab : a < b) :
    0 < logUniformPDFReal a b x ↔ x ∈ Ioo a b := by
  constructor
  · intro hpos
    by_contra hx
    rw [logUniformPDFReal_of_not (fun _ _ hax ↦
      le_of_not_gt fun hxb ↦ hx ⟨hax, hxb⟩)] at hpos
    exact (lt_irrefl 0) hpos
  · exact logUniformPDFReal_pos ha hab

/-- The extended log-uniform density is the nonnegative coercion of the real density. -/
theorem logUniformPDF_eq_ofReal (a b x : ℝ) :
    logUniformPDF a b x = ENNReal.ofReal (logUniformPDFReal a b x) :=
  (rfl)

@[simp]
theorem toReal_logUniformPDF (a b x : ℝ) :
    (logUniformPDF a b x).toReal = logUniformPDFReal a b x := by
  rw [logUniformPDF, ENNReal.toReal_ofReal (logUniformPDFReal_nonneg a b x)]

/-- The log-uniform density is jointly measurable in its endpoints and sample point. -/
theorem measurable_uncurry_logUniformPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ logUniformPDFReal p.1.1 p.1.2 p.2 := by
  unfold logUniformPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The extended log-uniform density is jointly measurable. -/
theorem measurable_uncurry_logUniformPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ logUniformPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_logUniformPDFReal.ennreal_ofReal

/-- The real log-uniform density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_logUniformPDFReal (a b : ℝ) : Measurable (logUniformPDFReal a b) :=
  by
    unfold logUniformPDFReal
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The extended log-uniform density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_logUniformPDF (a b : ℝ) : Measurable (logUniformPDF a b) :=
  (measurable_logUniformPDFReal a b).ennreal_ofReal

private theorem transform_logUniformPDF (ha : 0 < a) (hab : a < b) :
    (fun y ↦ ENNReal.ofReal |exp y| * logUniformPDF a b (exp y)) =ᵐ[volume]
      fun y ↦ pdf.uniformPDF (Ioc (log a) (log b)) y volume := by
  have hb : 0 < b := ha.trans hab
  have hlog : log a < log b := strictMonoOn_log ha hb hab
  filter_upwards [(volume : Measure ℝ).ae_ne (log b)] with y hy
  rw [logUniformPDF, uniformPDF_eq_ofReal_uniformPDFReal]
  by_cases hmem : y ∈ Ioc (log a) (log b)
  · have hlt : y < log b := lt_of_le_of_ne hmem.2 hy
    have hexp : exp y ∈ Ioo a b := ⟨
      by simpa only [exp_log ha] using Real.exp_lt_exp.mpr hmem.1,
      by simpa only [exp_log hb] using Real.exp_lt_exp.mpr hlt⟩
    rw [logUniformPDFReal_of_mem ha hab hexp, uniformPDFReal_of_mem hmem,
      abs_of_pos (exp_pos y), ← ENNReal.ofReal_mul (exp_nonneg y)]
    congr 1
    rw [log_div hb.ne' ha.ne']
    field_simp [exp_ne_zero y, sub_ne_zero.mpr hlog.ne]
  · have hnot : exp y ∉ Ioo a b := by
      intro h
      have hy' : y ∈ Ioo (log a) (log b) := ⟨
        Real.exp_lt_exp.mp (by simpa only [exp_log ha] using h.1),
        Real.exp_lt_exp.mp (by simpa only [exp_log hb] using h.2)⟩
      exact hmem ⟨hy'.1, hy'.2.le⟩
    rw [logUniformPDFReal_of_not (fun _ _ hax ↦
      le_of_not_gt fun hxb ↦ hnot ⟨hax, hxb⟩), uniformPDFReal_of_notMem hmem,
      ENNReal.ofReal_zero, mul_zero]

/-- The log-uniform law is Lebesgue measure weighted by its classical density, including the
invalid zero-measure branch. -/
theorem logUniformMeasure_eq_withDensity (a b : ℝ) :
    logUniformMeasure a b = volume.withDensity (logUniformPDF a b) := by
  by_cases h : 0 < a ∧ a < b
  · have hmap := MeasureTheory.map_withDensity_abs_deriv_mul (f := logUniformPDF a b)
      MeasurableSet.univ measurable_exp (fun y _ ↦ (hasDerivAt_exp y).hasDerivWithinAt)
      exp_injective.injOn
    simp only [Measure.restrict_univ, image_univ, range_exp] at hmap
    rw [withDensity_congr_ae (transform_logUniformPDF h.1 h.2)] at hmap
    have hind : (Ioi (0 : ℝ)).indicator (logUniformPDF a b) = logUniformPDF a b := by
      ext x
      by_cases hx : 0 < x
      · simp [hx]
      · have hpdf : logUniformPDF a b x = 0 := by
          rw [logUniformPDF, logUniformPDFReal_of_not]
          · simp
          · exact fun ha _ hax ↦ (hx (ha.trans hax)).elim
        simp [hx, hpdf]
    rw [logUniformMeasure_of_pos h.1 h.2, uniformMeasure_eq_withDensity, hmap,
      ← withDensity_indicator measurableSet_Ioi, hind]
  · have hpdf : logUniformPDF a b = 0 := by
      funext x
      rw [logUniformPDF, logUniformPDFReal_of_not]
      · simp
      · exact fun ha hab _ ↦ (h ⟨ha, hab⟩).elim
    rw [logUniformMeasure_of_not_pos h, hpdf, withDensity_zero]

/-- The topological support of a valid log-uniform law is the closed interval `[a, b]`. -/
@[simp]
theorem support_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    (logUniformMeasure a b).support = Icc a b := by
  rw [logUniformMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_logUniformPDF a b) isOpen_Ioo]
  · exact closure_Ioo hab.ne
  · ext x
    rw [Function.mem_support, Set.mem_Ioo]
    constructor
    · intro h
      by_contra hx
      exact h (by
        rw [logUniformPDF, logUniformPDFReal_of_not (fun _ _ hax ↦
          le_of_not_gt fun hxb ↦ hx ⟨hax, hxb⟩),
          ENNReal.ofReal_zero])
    · intro hx
      rw [logUniformPDF]
      exact (ENNReal.ofReal_pos.mpr (logUniformPDFReal_pos ha hab hx)).ne'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a log-uniform law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_logUniformMeasure (hX : HasLaw X (logUniformMeasure a b) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_logUniformPDF a b).aemeasurable
    (by rwa [logUniformMeasure_eq_withDensity] at hX)

/-- The canonical density of a log-uniform variable is `logUniformPDF` almost everywhere. -/
theorem pdf_eq_logUniformPDF_of_hasLaw_logUniformMeasure
    (hX : HasLaw X (logUniformMeasure a b) P) :
    pdf X P volume =ᵐ[volume] logUniformPDF a b :=
  pdf_eq_of_hasLaw_withDensity (measurable_logUniformPDF a b).aemeasurable
    (by rwa [logUniformMeasure_eq_withDensity] at hX)

/-- The Radon--Nikodym derivative of a log-uniform law is its named density. -/
theorem rnDeriv_logUniformMeasure (a b : ℝ) :
    (logUniformMeasure a b).rnDeriv volume =ᵐ[volume] logUniformPDF a b := by
  rw [logUniformMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_logUniformPDF a b)

/-! ### Cumulative distribution function -/

/-- The cdf of a valid log-uniform law, expressed by logarithmic interpolation between its
endpoints. -/
theorem cdf_logUniformMeasure_eq (ha : 0 < a) (hab : a < b) (x : ℝ) :
    cdf (logUniformMeasure a b) x =
      if x ≤ a then 0 else if b ≤ x then 1 else log (x / a) / log (b / a) := by
  have hb : 0 < b := ha.trans hab
  have hlog : log a < log b := strictMonoOn_log ha hb hab
  let _ : IsProbabilityMeasure (logUniformMeasure a b) :=
    isProbabilityMeasure_logUniformMeasure ha hab
  let _ : IsProbabilityMeasure (uniformMeasure (log a) (log b)) :=
    isProbabilityMeasure_uniformMeasure hlog
  by_cases hx : x ≤ 0
  · have hxa : x ≤ a := hx.trans ha.le
    rw [ite_eq_left hxa, cdf_eq_real, measureReal_def, logUniformMeasure_of_pos ha hab,
      Measure.map_apply measurable_exp measurableSet_Iic]
    have hpre : exp ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun h ↦ (not_le_of_gt (exp_pos y)) (h.trans hx)
    rw [hpre, measure_empty, ENNReal.toReal_zero]
  · have hxpos : 0 < x := lt_of_not_ge hx
    have hpre : exp ⁻¹' Iic x = Iic (log x) := by
      ext y
      simp only [mem_preimage, mem_Iic]
      exact (Real.le_log_iff_exp_le hxpos).symm
    rw [logUniformMeasure_of_pos ha hab, cdf_eq_real, measureReal_def,
      Measure.map_apply measurable_exp measurableSet_Iic, hpre, ← measureReal_def, ← cdf_eq_real,
      cdf_uniformMeasure hlog]
    by_cases hxa : x ≤ a
    · rw [ite_eq_left hxa, ite_eq_left ((Real.log_le_log_iff hxpos ha).2 hxa)]
    · have hax : a < x := lt_of_not_ge hxa
      rw [ite_eq_right hxa,
        ite_eq_right ((Real.log_le_log_iff hxpos ha).not.mpr (not_le_of_gt hax))]
      by_cases hbx : b ≤ x
      · rw [ite_eq_left hbx, ite_eq_left ((Real.log_le_log_iff hb hxpos).2 hbx)]
      · have hxb : x < b := lt_of_not_ge hbx
        rw [ite_eq_right hbx,
          ite_eq_right ((Real.log_le_log_iff hb hxpos).not.mpr (not_le_of_gt hxb))]
        rw [log_div hxpos.ne' ha.ne', log_div hb.ne' ha.ne']

/-! ### Quantiles -/

/-- The interior quantile of a valid log-uniform law is geometric interpolation between the
endpoints. -/
theorem quantile_logUniformMeasure (ha : 0 < a) (hab : a < b) (hu : u ∈ Ioo 0 1) :
    (logUniformMeasure a b).quantile u = a * (b / a) ^ u := by
  have hb : 0 < b := ha.trans hab
  have hlog : log a < log b := strictMonoOn_log ha hb hab
  let _ : IsProbabilityMeasure (uniformMeasure (log a) (log b)) :=
    isProbabilityMeasure_uniformMeasure hlog
  rw [logUniformMeasure_of_pos ha hab, Measure.quantile_map_exp hu.1 hu.2,
    quantile_uniformMeasure hlog hu]
  rw [Real.rpow_def_of_pos (div_pos hb ha), log_div hb.ne' ha.ne', exp_add, exp_log ha]

/-! ### Real-power moments -/

/-- Every real power is integrable under a log-uniform law, including for invalid endpoints where
the measure is zero. -/
theorem integrable_rpow_logUniformMeasure (a b q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (logUniformMeasure a b) := by
  by_cases h : 0 < a ∧ a < b
  · rw [logUniformMeasure_of_pos h.1 h.2,
      integrable_map_measure (by fun_prop) measurable_exp.aemeasurable]
    refine (integrable_exp_mul_id_uniformMeasure
      (a := log a) (b := log b) (t := q)).congr ?_
    filter_upwards with y
    simp only [Function.comp_apply, Real.rpow_def_of_pos (exp_pos y), log_exp]
    congr 1
    ring
  · simp [logUniformMeasure_of_not_pos h]

/-- The zeroth real-power moment of a valid log-uniform law is one. -/
theorem integral_rpow_logUniformMeasure_zero (ha : 0 < a) (hab : a < b) :
    ∫ x, x ^ (0 : ℝ) ∂logUniformMeasure a b = 1 := by
  have := isProbabilityMeasure_logUniformMeasure ha hab
  simp

/-- The nonzero real-power moments of a valid log-uniform law. -/
theorem integral_rpow_logUniformMeasure (ha : 0 < a) (hab : a < b) (hq : q ≠ 0) :
    ∫ x, x ^ q ∂logUniformMeasure a b =
      (b ^ q - a ^ q) / (q * log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  have hlog : log a < log b := strictMonoOn_log ha hb hab
  rw [logUniformMeasure_of_pos ha hab, integral_map measurable_exp.aemeasurable (by fun_prop)]
  have hmgf :
      ∫ y, exp y ^ q ∂uniformMeasure (log a) (log b) =
        mgf id (uniformMeasure (log a) (log b)) q := by
    rw [mgf]
    apply integral_congr_ae
    filter_upwards with y
    simp only [id_eq, ← exp_mul]
    congr 1
    ring
  rw [hmgf, mgf_id_uniformMeasure hlog hq]
  have hbq : exp (q * log b) = b ^ q := by
    rw [Real.rpow_def_of_pos hb]
    congr 1
    ring
  have haq : exp (q * log a) = a ^ q := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
    ring
  rw [hbq, haq, log_div hb.ne' ha.ne']
  ring

/-- The mean of a valid log-uniform law. -/
theorem integral_id_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    ∫ x, x ∂logUniformMeasure a b = (b - a) / log (b / a) := by
  simpa using integral_rpow_logUniformMeasure ha hab (q := 1) one_ne_zero

/-- The second raw moment of a valid log-uniform law. -/
theorem integral_sq_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    ∫ x, x ^ 2 ∂logUniformMeasure a b = (b ^ 2 - a ^ 2) / (2 * log (b / a)) := by
  simpa using integral_rpow_logUniformMeasure ha hab (q := 2) (by norm_num)

/-- The variance of a valid log-uniform law. -/
theorem variance_id_logUniformMeasure (ha : 0 < a) (hab : a < b) :
    Var[id; logUniformMeasure a b] =
      (b ^ 2 - a ^ 2) / (2 * log (b / a)) - ((b - a) / log (b / a)) ^ 2 := by
  let _ : IsProbabilityMeasure (logUniformMeasure a b) :=
    isProbabilityMeasure_logUniformMeasure ha hab
  have hLp : MemLp id 2 (logUniformMeasure a b) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (by
      simpa using integrable_rpow_logUniformMeasure a b 2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_logUniformMeasure ha hab,
    integral_id_logUniformMeasure ha hab]

/-! ### Exponential integrability -/

/-- Every exponential moment of a log-uniform law exists, including for invalid parameters where
the law is zero. -/
@[simp]
theorem integrableExpSet_id_logUniformMeasure (a b : ℝ) :
    integrableExpSet id (logUniformMeasure a b) = univ := by
  by_cases h : 0 < a ∧ a < b
  · rcases h with ⟨ha, hab⟩
    have hfinite : IsFiniteMeasure (logUniformMeasure a b) := by
      have := isProbabilityMeasure_logUniformMeasure ha hab
      infer_instance
    ext t
    simp only [mem_univ, iff_true, integrableExpSet, mem_ofPred_eq, id_eq]
    exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
      ((ae_mem_Ioc_logUniformMeasure a b).mono fun _ hy ↦ Ioc_subset_Icc_self hy)
  · rw [logUniformMeasure_of_not_pos h]
    ext t
    simp [integrableExpSet]

/-! ### Scaling and parameter measurability -/

/-- Multiplying a log-uniform variable by a positive constant multiplies both endpoints by that
constant. The identity also holds on the zero branch of invalid parameters. -/
theorem map_mul_logUniformMeasure {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (logUniformMeasure a b).map (c * ·) = logUniformMeasure (c * a) (c * b) := by
  by_cases h : 0 < a ∧ a < b
  · have hb : 0 < b := h.1.trans h.2
    have hca : 0 < c * a := mul_pos hc h.1
    have hcab : c * a < c * b := mul_lt_mul_of_pos_left h.2 hc
    have hlog : log a < log b := strictMonoOn_log h.1 hb h.2
    have hlogc : log (c * a) < log (c * b) :=
      strictMonoOn_log hca (hca.trans hcab) hcab
    have haffine :
        (fun y : ℝ ↦ log c + y) ∘ (fun z : ℝ ↦ log a + (log b - log a) * z) =
          fun z : ℝ ↦ log (c * a) + (log (c * b) - log (c * a)) * z := by
      funext z
      simp only [Function.comp_apply, log_mul hc.ne' h.1.ne', log_mul hc.ne' hb.ne']
      ring
    have huniform :
        (uniformMeasure (log a) (log b)).map (fun y ↦ log c + y) =
          uniformMeasure (log (c * a)) (log (c * b)) := by
      rw [← map_uniformMeasure_affine hlog, Measure.map_map (by fun_prop) (by fun_prop),
        haffine, map_uniformMeasure_affine hlogc]
    have hcomp : (c * ·) ∘ exp = exp ∘ fun y ↦ log c + y := by
      funext y
      simp only [Function.comp_apply, exp_add, exp_log hc]
    rw [logUniformMeasure_of_pos h.1 h.2, logUniformMeasure_of_pos hca hcab,
      Measure.map_map (by fun_prop) measurable_exp, hcomp,
      ← Measure.map_map measurable_exp (by fun_prop), huniform]
  · have h' : ¬ (0 < c * a ∧ c * a < c * b) := fun h' ↦
      h ⟨pos_of_mul_pos_right h'.1 hc.le, lt_of_mul_lt_mul_left h'.2 hc.le⟩
    rw [logUniformMeasure_of_not_pos h, logUniformMeasure_of_not_pos h', Measure.map_zero]

/-- If `X` is log-uniform on `(a, b]`, then `c * X` is log-uniform on `(c * a, c * b]`
for `c > 0`. -/
theorem hasLaw_mul_logUniformMeasure {c : ℝ} (hc : 0 < c)
    (hX : HasLaw X (logUniformMeasure a b) P) :
    HasLaw (fun ω ↦ c * X ω) (logUniformMeasure (c * a) (c * b)) P := by
  rw [← map_mul_logUniformMeasure hc]
  exact (hasLaw_map (by fun_prop : Measurable (c * · : ℝ → ℝ)).aemeasurable).comp hX

/-- The log-uniform family is measurable in its two endpoints, including the invalid zero-law
branch. -/
@[fun_prop]
theorem measurable_logUniformMeasure :
    Measurable fun p : ℝ × ℝ ↦ logUniformMeasure p.1 p.2 := by
  simp only [logUniformMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_logUniformPDF

end TauCeti.Probability
