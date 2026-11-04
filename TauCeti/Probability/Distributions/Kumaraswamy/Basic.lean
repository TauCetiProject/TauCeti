/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Beta.Cdf
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Cdf
import TauCeti.Probability.Density

/-!
# The Kumaraswamy distribution

For positive shape parameters `a` and `b`, the Kumaraswamy law on the unit interval has density
`a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)` on `(0, 1)`. Unlike the Beta law it has the
elementary cumulative distribution function `1 - (1 - x ^ a) ^ b` on `[0, 1]`.

This file defines the law by its density, which vanishes at invalid parameters, and proves its
density API and parameter measurability. The central identity is that `X ^ a` has the Beta
`(1, b)` law when `X` is Kumaraswamy `(a, b)`. It is proved by the substitution `y = x ^ a`, and
it yields normalization, the cumulative distribution function, and the moments in
`TauCeti.Probability.Distributions.Kumaraswamy.Moments`.

## Main definitions

* `TauCeti.Probability.kumaraswamyMeasure` — the Kumaraswamy law;
* `TauCeti.Probability.kumaraswamyPDFReal` and `TauCeti.Probability.kumaraswamyPDF` — its
  densities.

## Main results

* `TauCeti.Probability.map_rpow_kumaraswamyMeasure` — the power `x ^ a` pushes the Kumaraswamy
  `(a, b)` law to the Beta `(1, b)` law;
* `TauCeti.Probability.kumaraswamyMeasure_one_left` — the Kumaraswamy `(1, b)` law is Beta
  `(1, b)`;
* `TauCeti.Probability.isProbabilityMeasure_kumaraswamyMeasure_iff` — the law is a probability
  measure exactly at positive parameters;
* `TauCeti.Probability.support_kumaraswamyMeasure` — the topological support is `[0, 1]`;
* `TauCeti.Probability.integrable_kumaraswamyMeasure_iff` and
  `TauCeti.Probability.integral_kumaraswamyMeasure_eq` — integrability and integration against the
  law, transferred to the real density;
* `TauCeti.Probability.cdf_kumaraswamyMeasure_of_mem_Icc` — the cdf `1 - (1 - x ^ a) ^ b` on the
  unit interval, and `TauCeti.Probability.cdf_kumaraswamyMeasure_eq` its closed form everywhere;
* `TauCeti.Probability.measurable_kumaraswamyMeasure` — joint measurability in the parameters.

## References

* P. Kumaraswamy, *A generalized probability density function for double-bounded random
  processes*, Journal of Hydrology 46 (1980), 79–88.
* M. C. Jones, *Kumaraswamy's distribution: A beta-type distribution with some tractability
  advantages*, Statistical Methodology 6 (2009), 70–81.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {a b x : ℝ}

/-! ### Density -/

/-- The real-valued Kumaraswamy density `a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)` on the open
unit interval. It vanishes off `(0, 1)` and unless both shape parameters are positive. -/
def kumaraswamyPDFReal (a b x : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b ∧ 0 < x ∧ x < 1 then
    a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)
  else 0

/-- The extended-nonnegative-valued Kumaraswamy density. -/
def kumaraswamyPDF (a b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (kumaraswamyPDFReal a b x)

/-- The Kumaraswamy density is the nonnegative coercion of its real-valued version. -/
theorem kumaraswamyPDF_eq_ofReal (a b x : ℝ) :
    kumaraswamyPDF a b x = ENNReal.ofReal (kumaraswamyPDFReal a b x) := (rfl)

/-- At valid parameters and inside the unit interval, the real Kumaraswamy density has its
classical formula. -/
@[simp]
theorem kumaraswamyPDFReal_of_mem_Ioo (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Ioo 0 1) :
    kumaraswamyPDFReal a b x = a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1) := by
  rw [kumaraswamyPDFReal, ite_eq_left ⟨ha, hb, hx.1, hx.2⟩]

/-- The real Kumaraswamy density vanishes outside the open unit interval. -/
@[simp]
theorem kumaraswamyPDFReal_of_notMem_Ioo (hx : x ∉ Ioo 0 1) (a b : ℝ) :
    kumaraswamyPDFReal a b x = 0 :=
  ite_eq_right fun h ↦ hx ⟨h.2.2.1, h.2.2.2⟩

/-- The real Kumaraswamy density vanishes unless both shape parameters are positive. -/
@[simp]
theorem kumaraswamyPDFReal_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) (x : ℝ) :
    kumaraswamyPDFReal a b x = 0 :=
  ite_eq_right fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The real Kumaraswamy density is positive on the open unit interval at valid parameters. -/
theorem kumaraswamyPDFReal_pos (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Ioo 0 1) :
    0 < kumaraswamyPDFReal a b x := by
  rw [kumaraswamyPDFReal_of_mem_Ioo ha hb hx]
  have hxa : x ^ a < 1 := Real.rpow_lt_one hx.1.le hx.2 ha
  exact mul_pos (mul_pos (mul_pos ha hb) (Real.rpow_pos_of_pos hx.1 _))
    (Real.rpow_pos_of_pos (sub_pos.mpr hxa) _)

/-- At valid parameters, the real Kumaraswamy density is positive exactly on the open unit
interval. -/
theorem kumaraswamyPDFReal_pos_iff (ha : 0 < a) (hb : 0 < b) :
    0 < kumaraswamyPDFReal a b x ↔ x ∈ Ioo 0 1 := by
  refine ⟨fun h ↦ ?_, kumaraswamyPDFReal_pos ha hb⟩
  by_contra hx
  rw [kumaraswamyPDFReal_of_notMem_Ioo hx] at h
  exact h.false

/-- The real Kumaraswamy density is nonnegative. -/
theorem kumaraswamyPDFReal_nonneg (a b x : ℝ) : 0 ≤ kumaraswamyPDFReal a b x := by
  by_cases h : 0 < a ∧ 0 < b ∧ 0 < x ∧ x < 1
  · exact (kumaraswamyPDFReal_pos h.1 h.2.1 ⟨h.2.2.1, h.2.2.2⟩).le
  · rw [kumaraswamyPDFReal, ite_eq_right h]

/-- Converting the Kumaraswamy density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_kumaraswamyPDF (a b x : ℝ) :
    (kumaraswamyPDF a b x).toReal = kumaraswamyPDFReal a b x :=
  ENNReal.toReal_ofReal (kumaraswamyPDFReal_nonneg a b x)

/-- At valid parameters and inside the unit interval, the Kumaraswamy density has its classical
formula. -/
@[simp]
theorem kumaraswamyPDF_of_mem_Ioo (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Ioo 0 1) :
    kumaraswamyPDF a b x = ENNReal.ofReal (a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)) := by
  rw [kumaraswamyPDF_eq_ofReal, kumaraswamyPDFReal_of_mem_Ioo ha hb hx]

/-- The Kumaraswamy density vanishes outside the open unit interval. -/
@[simp]
theorem kumaraswamyPDF_of_notMem_Ioo (hx : x ∉ Ioo 0 1) (a b : ℝ) : kumaraswamyPDF a b x = 0 := by
  rw [kumaraswamyPDF_eq_ofReal, kumaraswamyPDFReal_of_notMem_Ioo hx, ENNReal.ofReal_zero]

/-- The Kumaraswamy density vanishes unless both shape parameters are positive. -/
@[simp]
theorem kumaraswamyPDF_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) (x : ℝ) : kumaraswamyPDF a b x = 0 := by
  rw [kumaraswamyPDF_eq_ofReal, kumaraswamyPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The Kumaraswamy density is jointly measurable in both shape parameters and the sample
point. -/
@[fun_prop]
theorem measurable_uncurry_kumaraswamyPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ kumaraswamyPDFReal q.1.1 q.1.2 q.2 := by
  unfold kumaraswamyPDFReal
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  have hzero : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ) := measurable_const
  have hone : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (1 : ℝ) := measurable_const
  exact (measurableSet_lt hzero measurable_fst.fst).inter
    ((measurableSet_lt hzero measurable_fst.snd).inter
      ((measurableSet_lt hzero measurable_snd).inter (measurableSet_lt measurable_snd hone)))

/-- The extended-nonnegative Kumaraswamy density is jointly measurable in both shape parameters
and the sample point. -/
@[fun_prop]
theorem measurable_uncurry_kumaraswamyPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ kumaraswamyPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_kumaraswamyPDFReal.ennreal_ofReal

/-- The real Kumaraswamy density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_kumaraswamyPDFReal (a b : ℝ) : Measurable (kumaraswamyPDFReal a b) :=
  measurable_uncurry_kumaraswamyPDFReal.comp (measurable_prodMk_left (x := (a, b)))

/-- The Kumaraswamy density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_kumaraswamyPDF (a b : ℝ) : Measurable (kumaraswamyPDF a b) :=
  (measurable_kumaraswamyPDFReal a b).ennreal_ofReal

/-! ### The law -/

/-- The Kumaraswamy law with shape parameters `a` and `b`: Lebesgue measure weighted by
`kumaraswamyPDF a b`. It is zero unless both parameters are positive. -/
def kumaraswamyMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (kumaraswamyPDF a b)

/-- The Kumaraswamy law is Lebesgue measure weighted by its density. -/
theorem kumaraswamyMeasure_eq_withDensity (a b : ℝ) :
    kumaraswamyMeasure a b = volume.withDensity (kumaraswamyPDF a b) := (rfl)

/-- At invalid parameters, the Kumaraswamy law is zero. -/
@[simp]
theorem kumaraswamyMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) : kumaraswamyMeasure a b = 0 := by
  have hpdf : kumaraswamyPDF a b = 0 := funext (kumaraswamyPDF_of_not_pos h)
  rw [kumaraswamyMeasure_eq_withDensity, hpdf, withDensity_zero]

/-- The Kumaraswamy law is its density against Lebesgue measure on the open unit interval. -/
theorem kumaraswamyMeasure_eq_withDensity_restrict_Ioo (a b : ℝ) :
    kumaraswamyMeasure a b = (volume.restrict (Ioo 0 1)).withDensity (kumaraswamyPDF a b) := by
  rw [← withDensity_indicator measurableSet_Ioo, kumaraswamyMeasure_eq_withDensity]
  congr 1
  funext x
  by_cases hx : x ∈ Ioo 0 1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, kumaraswamyPDF_of_notMem_Ioo hx]

/-- A Kumaraswamy law lies almost everywhere in the open unit interval, for all parameter
values. -/
theorem ae_mem_Ioo_kumaraswamyMeasure (a b : ℝ) :
    ∀ᵐ x ∂kumaraswamyMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [kumaraswamyMeasure_eq_withDensity_restrict_Ioo]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- A Kumaraswamy law is carried by the closed unit interval. -/
theorem ae_mem_Icc_kumaraswamyMeasure (a b : ℝ) :
    ∀ᵐ x ∂kumaraswamyMeasure a b, x ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [ae_mem_Ioo_kumaraswamyMeasure a b] with x hx
  exact Ioo_subset_Icc_self hx

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against a Kumaraswamy law exactly when
its density-weighted version is Lebesgue integrable. This holds at every parameter, the zero
measure included. -/
theorem integrable_kumaraswamyMeasure_iff (a b : ℝ) {g : ℝ → E} :
    Integrable g (kumaraswamyMeasure a b) ↔
      Integrable (fun x ↦ kumaraswamyPDFReal a b x • g x) := by
  rw [kumaraswamyMeasure_eq_withDensity, funext (kumaraswamyPDF_eq_ofReal a b)]
  exact Probability.integrable_withDensity_ofReal_iff
    (measurable_kumaraswamyPDFReal a b).aemeasurable (ae_of_all _ (kumaraswamyPDFReal_nonneg a b))

/-- **Integral transfer.** An integral against a Kumaraswamy law is the density-weighted Lebesgue
integral. This holds at every parameter, the zero measure included. -/
theorem integral_kumaraswamyMeasure_eq (a b : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂kumaraswamyMeasure a b = ∫ x, kumaraswamyPDFReal a b x • g x := by
  rw [kumaraswamyMeasure_eq_withDensity, funext (kumaraswamyPDF_eq_ofReal a b)]
  exact Probability.integral_withDensity_ofReal (measurable_kumaraswamyPDFReal a b).aemeasurable
    (ae_of_all _ (kumaraswamyPDFReal_nonneg a b)) g

end Transfer

/-- At positive parameters, the topological support of the Kumaraswamy law is the closed unit
interval. -/
theorem support_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    (kumaraswamyMeasure a b).support = Icc 0 1 := by
  have hsupp : Function.support (kumaraswamyPDF a b) = Ioo 0 1 := by
    ext x
    rw [Function.mem_support]
    constructor
    · intro hx
      by_contra h
      exact hx (kumaraswamyPDF_of_notMem_Ioo h a b)
    · intro hx
      rw [kumaraswamyPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
      exact kumaraswamyPDFReal_pos ha hb hx
  rw [kumaraswamyMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_kumaraswamyPDF a b) isOpen_Ioo hsupp,
    closure_Ioo zero_ne_one]

/-! ### The power map to the Beta `(1, b)` law -/

/-- On the open unit interval, the Kumaraswamy density is the Beta `(1, b)` density at `x ^ a`
times the Jacobian `a * x ^ (a - 1)` of the substitution `y = x ^ a`. -/
private theorem kumaraswamyPDF_eq_jacobian_mul_betaPDF (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Ioo 0 1) :
    kumaraswamyPDF a b x = ENNReal.ofReal |a * x ^ (a - 1)| * betaPDF 1 b (x ^ a) := by
  have hxa : x ^ a < 1 := Real.rpow_lt_one hx.1.le hx.2 ha
  have hjac : 0 < a * x ^ (a - 1) := mul_pos ha (Real.rpow_pos_of_pos hx.1 _)
  rw [kumaraswamyPDF_of_mem_Ioo ha hb hx,
    betaPDF_of_pos_lt_one (Real.rpow_pos_of_pos hx.1 a) hxa, abs_of_pos hjac,
    ← ENNReal.ofReal_mul hjac.le, beta_comm, beta_one_right hb, sub_self, Real.rpow_zero]
  congr 1
  field_simp

/-- **Kumaraswamy and Beta laws.** If `X` is Kumaraswamy `(a, b)`, then `X ^ a` is Beta
`(1, b)`. -/
theorem map_rpow_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    (kumaraswamyMeasure a b).map (fun x ↦ x ^ a) = betaMeasure 1 b := by
  have hweight : kumaraswamyPDF a b =ᵐ[volume.restrict (Ioo 0 1)]
      fun x ↦ ENNReal.ofReal |a * x ^ (a - 1)| * betaPDF 1 b (x ^ a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact kumaraswamyPDF_eq_jacobian_mul_betaPDF ha hb hx
  rw [kumaraswamyMeasure_eq_withDensity_restrict_Ioo, withDensity_congr_ae hweight,
    TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul measurableSet_Ioo (by fun_prop)
      (fun x hx ↦ (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).hasDerivWithinAt)
      ((Real.rpow_left_injOn ha.ne').mono fun x hx ↦ le_of_lt hx.1),
    Real.image_rpow_Ioo_zero_one ha, ← betaMeasure_eq_withDensity_restrict_Ioo]

/-- The Kumaraswamy law is a probability measure at positive parameters. -/
theorem isProbabilityMeasure_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (kumaraswamyMeasure a b) := by
  have := isProbabilityMeasureBeta zero_lt_one hb
  constructor
  rw [← preimage_univ (f := fun x : ℝ ↦ x ^ a), ← Measure.map_apply (by fun_prop) .univ,
    map_rpow_kumaraswamyMeasure ha hb, measure_univ]

/-- The Kumaraswamy density has total mass one at positive parameters. -/
theorem lintegral_kumaraswamyPDF_eq_one (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, kumaraswamyPDF a b x = 1 := by
  have := isProbabilityMeasure_kumaraswamyMeasure ha hb
  rw [← setLIntegral_univ, ← withDensity_apply _ .univ, ← kumaraswamyMeasure_eq_withDensity,
    measure_univ]

/-- The real Kumaraswamy density integrates to one at positive parameters. -/
theorem integral_kumaraswamyPDFReal (ha : 0 < a) (hb : 0 < b) :
    ∫ x, kumaraswamyPDFReal a b x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (kumaraswamyPDFReal_nonneg a b))
    (measurable_kumaraswamyPDFReal a b).aestronglyMeasurable]
  simp only [← kumaraswamyPDF_eq_ofReal, lintegral_kumaraswamyPDF_eq_one ha hb, ENNReal.toReal_one]

/-- The Kumaraswamy law is a probability measure exactly at positive parameters. -/
@[simp]
theorem isProbabilityMeasure_kumaraswamyMeasure_iff :
    IsProbabilityMeasure (kumaraswamyMeasure a b) ↔ 0 < a ∧ 0 < b := by
  refine ⟨fun h ↦ ?_, fun h ↦ isProbabilityMeasure_kumaraswamyMeasure h.1 h.2⟩
  by_contra hab
  rw [kumaraswamyMeasure_of_not_pos hab] at h
  exact not_isProbabilityMeasure_zero h

/-- With first shape parameter `1`, the Kumaraswamy law is the Beta `(1, b)` law. -/
@[simp]
theorem kumaraswamyMeasure_one_left (hb : 0 < b) : kumaraswamyMeasure 1 b = betaMeasure 1 b := by
  simpa using map_rpow_kumaraswamyMeasure zero_lt_one hb

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` has a Kumaraswamy `(a, b)` law, then `X ^ a` has the Beta `(1, b)` law. -/
theorem hasLaw_rpow_of_hasLaw_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b)
    (hX : HasLaw X (kumaraswamyMeasure a b) P) :
    HasLaw (fun ω ↦ X ω ^ a) (betaMeasure 1 b) P :=
  HasLaw.fun_comp (Y := fun x : ℝ ↦ x ^ a)
    ⟨by fun_prop, map_rpow_kumaraswamyMeasure ha hb⟩ hX

/-- A random variable with a Kumaraswamy law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_kumaraswamyMeasure (hX : HasLaw X (kumaraswamyMeasure a b) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_kumaraswamyPDF a b).aemeasurable hX

/-- The density of a random variable with a Kumaraswamy law is `kumaraswamyPDF`. -/
theorem pdf_eq_kumaraswamyPDF_of_hasLaw_kumaraswamyMeasure
    (hX : HasLaw X (kumaraswamyMeasure a b) P) :
    pdf X P volume =ᵐ[volume] kumaraswamyPDF a b :=
  pdf_eq_of_hasLaw_withDensity (measurable_kumaraswamyPDF a b).aemeasurable hX

end RandomVariables

/-- The Radon–Nikodym derivative of a Kumaraswamy law with respect to Lebesgue measure. -/
theorem rnDeriv_kumaraswamyMeasure (a b : ℝ) :
    (kumaraswamyMeasure a b).rnDeriv volume =ᵐ[volume] kumaraswamyPDF a b :=
  Measure.rnDeriv_withDensity volume (measurable_kumaraswamyPDF a b)

/-- The Kumaraswamy family is jointly measurable in its two shape parameters. -/
@[fun_prop]
theorem measurable_kumaraswamyMeasure :
    Measurable fun p : ℝ × ℝ ↦ kumaraswamyMeasure p.1 p.2 := by
  simpa only [kumaraswamyMeasure_eq_withDensity] using
    measurable_withDensity (μ := volume) measurable_uncurry_kumaraswamyPDF

/-! ### Cumulative distribution function -/

/-- On the nonnegative half-line, the Kumaraswamy cdf is the Beta `(1, b)` cdf at `x ^ a`. -/
theorem cdf_kumaraswamyMeasure_of_nonneg (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) :
    cdf (kumaraswamyMeasure a b) x = regularizedIncompleteBeta 1 b (x ^ a) := by
  have := isProbabilityMeasure_kumaraswamyMeasure ha hb
  have hset : Iic x =ᵐ[kumaraswamyMeasure a b] (fun y : ℝ ↦ y ^ a) ⁻¹' Iic (x ^ a) := by
    filter_upwards [ae_mem_Ioo_kumaraswamyMeasure a b] with y hy
    exact propext (Real.rpow_le_rpow_iff hy.1.le hx ha).symm
  rw [cdf_eq_real, ← measureReal_Iic_betaMeasure zero_lt_one hb,
    ← map_rpow_kumaraswamyMeasure ha hb, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, measure_congr hset]

/-- On the unit interval, the Kumaraswamy cdf is `1 - (1 - x ^ a) ^ b`. -/
theorem cdf_kumaraswamyMeasure_of_mem_Icc (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Icc 0 1) :
    cdf (kumaraswamyMeasure a b) x = 1 - (1 - x ^ a) ^ b := by
  rw [cdf_kumaraswamyMeasure_of_nonneg ha hb hx.1, regularizedIncompleteBeta_one_left hb
    (Real.rpow_nonneg hx.1 a) (Real.rpow_le_one hx.1 hx.2 ha.le)]

/-- The Kumaraswamy cdf vanishes on the nonpositive half-line. -/
theorem cdf_kumaraswamyMeasure_of_nonpos (ha : 0 < a) (hb : 0 < b) (hx : x ≤ 0) :
    cdf (kumaraswamyMeasure a b) x = 0 := by
  refine le_antisymm ?_ (cdf_nonneg _ x)
  calc
    cdf (kumaraswamyMeasure a b) x ≤ cdf (kumaraswamyMeasure a b) 0 := (cdf _).mono hx
    _ = 0 := by
      rw [cdf_kumaraswamyMeasure_of_mem_Icc ha hb ⟨le_rfl, zero_le_one⟩,
        Real.zero_rpow ha.ne', sub_zero, Real.one_rpow, sub_self]

/-- The Kumaraswamy cdf is one from the upper endpoint `1` on. -/
theorem cdf_kumaraswamyMeasure_of_one_le (ha : 0 < a) (hb : 0 < b) (hx : 1 ≤ x) :
    cdf (kumaraswamyMeasure a b) x = 1 := by
  refine le_antisymm (cdf_le_one _ x) ?_
  calc
    (1 : ℝ) = cdf (kumaraswamyMeasure a b) 1 := by
      rw [cdf_kumaraswamyMeasure_of_mem_Icc ha hb ⟨zero_le_one, le_rfl⟩, Real.one_rpow,
        sub_self, Real.zero_rpow hb.ne', sub_zero]
    _ ≤ cdf (kumaraswamyMeasure a b) x := (cdf _).mono hx

/-- The Kumaraswamy cdf in closed form at every point: `0` on the nonpositive half-line,
`1 - (1 - x ^ a) ^ b` on `(0, 1)`, and `1` from the upper endpoint on. -/
@[simp]
theorem cdf_kumaraswamyMeasure_eq (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    cdf (kumaraswamyMeasure a b) x =
      if x ≤ 0 then 0 else if x < 1 then 1 - (1 - x ^ a) ^ b else 1 := by
  split_ifs with h₀ h₁
  · exact cdf_kumaraswamyMeasure_of_nonpos ha hb h₀
  · exact cdf_kumaraswamyMeasure_of_mem_Icc ha hb ⟨le_of_not_ge h₀, h₁.le⟩
  · exact cdf_kumaraswamyMeasure_of_one_le ha hb (le_of_not_gt h₁)

/-- The Kumaraswamy cdf is continuous. -/
theorem continuous_cdf_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    Continuous (cdf (kumaraswamyMeasure a b)) := by
  have := isProbabilityMeasure_kumaraswamyMeasure ha hb
  have : NullSingletonClass (kumaraswamyMeasure a b) := by
    rw [kumaraswamyMeasure_eq_withDensity]
    infer_instance
  exact Measure.continuous_cdf_of_noAtoms _

end TauCeti.Probability
