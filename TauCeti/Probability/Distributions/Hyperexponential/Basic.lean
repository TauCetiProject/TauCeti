/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Density
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Exponential.Measurability
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Hyperexponential distributions

A hyperexponential law is a finite probability mixture of exponential laws. Only components
with positive weight need positive rates; rates of zero-weight components are irrelevant.
The law and its densities are zero if an active rate is nonpositive.

This file provides the construction, normalization, density and Radon--Nikodym interfaces,
parameter measurability, cdf, exact topological support, and finite-mixture integration.
The mixture is almost surely positive, while zero belongs to its topological support when
every active rate is positive.

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4,
  on phase-type distributions and finite mixtures of exponentials.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]
variable {p : StdSimplex ℝ≥0 ι} {r : ι → ℝ} {x : ℝ}

/-- The finite mixture of exponential laws with weights `p` and rates `r`. It is zero unless
every positive-weight component has positive rate. -/
def hyperexponentialMeasure (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) : Measure ℝ :=
  if ∀ i, 0 < p.weights i → 0 < r i then
    ∑ i, (p.weights i : ℝ≥0∞) • expMeasure (r i)
  else 0

/-- On valid parameters, the law is the weighted sum of its exponential components. -/
theorem hyperexponentialMeasure_of_pos (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    hyperexponentialMeasure p r = ∑ i, (p.weights i : ℝ≥0∞) • expMeasure (r i) := by
  rw [hyperexponentialMeasure, ite_eq_left hr]

/-- A nonpositive active rate gives the zero law. -/
@[simp]
theorem hyperexponentialMeasure_of_not_pos (hr : ¬ ∀ i, 0 < p.weights i → 0 < r i) :
    hyperexponentialMeasure p r = 0 := by
  rw [hyperexponentialMeasure, ite_eq_right hr]

/-- The finite mixture is the categorical bind of the exponential family. -/
theorem hyperexponentialMeasure_eq_bind [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    hyperexponentialMeasure p r = (categoricalMeasure p).bind (fun i ↦ expMeasure (r i)) := by
  ext s hs
  rw [hyperexponentialMeasure_of_pos hr, Measure.finsetSum_apply,
    Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp only [categoricalMeasure_singleton, Measure.smul_apply, smul_eq_mul, mul_comm]

/-- Valid hyperexponential laws have total mass one, including weights equal to zero. -/
theorem isProbabilityMeasure_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    IsProbabilityMeasure (hyperexponentialMeasure p r) := by
  constructor
  rw [hyperexponentialMeasure_of_pos hr, Measure.finsetSum_apply]
  have hterm (i : ι) : (p.weights i : ℝ≥0∞) * expMeasure (r i) univ = p.weights i := by
    by_cases hi : p.weights i = 0
    · simp [hi]
    · let _ := isProbabilityMeasure_expMeasure (hr i (pos_iff_ne_zero.mpr hi))
      simp
  simp only [Measure.smul_apply, smul_eq_mul, hterm]
  exact_mod_cast p.total_of_fintype

/-- Every totalized hyperexponential law is finite. -/
instance (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    IsFiniteMeasure (hyperexponentialMeasure p r) := by
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · let _ := isProbabilityMeasure_hyperexponentialMeasure hr
    infer_instance
  · rw [hyperexponentialMeasure_of_not_pos hr]
    infer_instance

/-- The active-rate condition is exactly the probability parameter range. -/
@[simp]
theorem isProbabilityMeasure_hyperexponentialMeasure_iff :
    IsProbabilityMeasure (hyperexponentialMeasure p r) ↔
      ∀ i, 0 < p.weights i → 0 < r i := by
  refine ⟨fun h ↦ ?_, isProbabilityMeasure_hyperexponentialMeasure⟩
  by_contra hr
  let _ := h
  exact (IsProbabilityMeasure.ne_zero (hyperexponentialMeasure p r))
    (hyperexponentialMeasure_of_not_pos hr)

/-- The real density of a hyperexponential law, with value zero off the positive half-line
and outside the valid parameter range. -/
def hyperexponentialPDFReal (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (x : ℝ) : ℝ :=
  if (∀ i, 0 < p.weights i → 0 < r i) ∧ 0 < x then
    ∑ i, (p.weights i : ℝ) * r i * exp (-(r i * x))
  else 0

/-- The extended nonnegative density of a hyperexponential law. -/
def hyperexponentialPDF (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hyperexponentialPDFReal p r x)

/-- The extended density is the nonnegative coercion of the real density. -/
theorem hyperexponentialPDF_eq_ofReal (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (x : ℝ) :
    hyperexponentialPDF p r x = ENNReal.ofReal (hyperexponentialPDFReal p r x) := (rfl)

/-- On the positive half-line the density is the weighted sum of exponential densities. -/
@[simp]
theorem hyperexponentialPDFReal_of_pos (hr : ∀ i, 0 < p.weights i → 0 < r i) (hx : 0 < x) :
    hyperexponentialPDFReal p r x =
      ∑ i, (p.weights i : ℝ) * r i * exp (-(r i * x)) := by
  rw [hyperexponentialPDFReal, ite_eq_left ⟨hr, hx⟩]

/-- The density vanishes unless the parameters are valid and the sample point is positive. -/
@[simp]
theorem hyperexponentialPDFReal_of_not_pos
    (h : ¬ ((∀ i, 0 < p.weights i → 0 < r i) ∧ 0 < x)) :
    hyperexponentialPDFReal p r x = 0 := by
  simp [hyperexponentialPDFReal, h]

omit [Fintype ι] in
private theorem component_nonneg (hr : ∀ i, 0 < p.weights i → 0 < r i) (i : ι) (x : ℝ) :
    0 ≤ (p.weights i : ℝ) * r i * exp (-(r i * x)) := by
  by_cases hi : p.weights i = 0
  · simp [hi]
  · exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (hr i (pos_iff_ne_zero.mpr hi)).le)
      (exp_nonneg _)

/-- The real hyperexponential density is nonnegative at every parameter and sample point. -/
theorem hyperexponentialPDFReal_nonneg (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (x : ℝ) :
    0 ≤ hyperexponentialPDFReal p r x := by
  unfold hyperexponentialPDFReal
  split_ifs with h
  · exact Finset.sum_nonneg fun i _ ↦ component_nonneg h.1 i x
  · exact le_rfl

/-- Coercing the extended density back to the reals recovers the real density. -/
@[simp]
theorem toReal_hyperexponentialPDF (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (x : ℝ) :
    (hyperexponentialPDF p r x).toReal = hyperexponentialPDFReal p r x :=
  ENNReal.toReal_ofReal (hyperexponentialPDFReal_nonneg p r x)

/-- The density is measurable jointly in its weights, rates, and sample point. -/
@[fun_prop]
theorem measurable_uncurry_hyperexponentialPDFReal :
    Measurable fun z : (StdSimplex ℝ≥0 ι × (ι → ℝ)) × ℝ ↦
      hyperexponentialPDFReal z.1.1 z.1.2 z.2 := by
  have hw (i : ι) : Measurable fun p : StdSimplex ℝ≥0 ι ↦ p.weights i :=
    (measurable_pi_apply i).comp StdSimplex.measurable_toFun_comp_weights
  unfold hyperexponentialPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The extended density is jointly measurable. -/
@[fun_prop]
theorem measurable_uncurry_hyperexponentialPDF :
    Measurable fun z : (StdSimplex ℝ≥0 ι × (ι → ℝ)) × ℝ ↦
      hyperexponentialPDF z.1.1 z.1.2 z.2 :=
  measurable_uncurry_hyperexponentialPDFReal.ennreal_ofReal

/-- The real density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_hyperexponentialPDFReal (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    Measurable (hyperexponentialPDFReal p r) :=
  measurable_uncurry_hyperexponentialPDFReal.comp
    ((measurable_const (a := (p, r))).prodMk measurable_id)

/-- The extended density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_hyperexponentialPDF (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    Measurable (hyperexponentialPDF p r) :=
  (measurable_hyperexponentialPDFReal p r).ennreal_ofReal

/-- Hyperexponential laws are measurable in all their parameters, including invalid rates
and zero weights. -/
@[fun_prop]
theorem measurable_hyperexponentialMeasure :
    Measurable fun z : StdSimplex ℝ≥0 ι × (ι → ℝ) ↦ hyperexponentialMeasure z.1 z.2 := by
  have hw (i : ι) : Measurable fun p : StdSimplex ℝ≥0 ι ↦ p.weights i :=
    (measurable_pi_apply i).comp StdSimplex.measurable_toFun_comp_weights
  unfold hyperexponentialMeasure
  apply Measurable.ite (by measurability) _ measurable_const
  apply Finset.measurable_sum
  intro i hi
  apply Measure.measurable_measure.mpr
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact (measurable_coe_nnreal_ennreal.comp ((hw i).comp measurable_fst)).mul
    ((Measure.measurable_coe hs).comp
      (measurable_expMeasure.comp ((measurable_pi_apply i).comp measurable_snd)))

/-- The law is volume weighted by its named density, also for invalid parameters. -/
theorem hyperexponentialMeasure_eq_withDensity (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    hyperexponentialMeasure p r = volume.withDensity (hyperexponentialPDF p r) := by
  classical
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · have hpdf : hyperexponentialPDF p r =ᵐ[volume]
        fun x ↦ ∑ i, (p.weights i : ℝ≥0∞) * exponentialPDF (r i) x := by
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
      rcases lt_or_gt_of_ne hx with hx | hx
      · simp [hyperexponentialPDF, hyperexponentialPDFReal, hx.not_gt,
          exponentialPDF_of_neg hx]
      · rw [hyperexponentialPDF, hyperexponentialPDFReal_of_pos hr hx,
          ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ component_nonneg hr i x)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [exponentialPDF_of_nonneg hx.le, mul_assoc,
          ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [withDensity_congr_ae hpdf, hyperexponentialMeasure_of_pos hr]
    have hsum := withDensity_tsum (μ := (volume : Measure ℝ))
      (f := fun i x ↦ (p.weights i : ℝ≥0∞) * exponentialPDF (r i) x)
      (fun i ↦ measurable_const.mul ((measurable_exponentialPDFReal (r i)).ennreal_ofReal))
    simp only [tsum_fintype, Measure.sum_fintype, Finset.sum_fn] at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [expMeasure_eq_withDensity]
    simpa only [Pi.smul_def, smul_eq_mul] using
      (withDensity_smul' (μ := (volume : Measure ℝ)) (p.weights i : ℝ≥0∞)
        (exponentialPDF (r i)) ENNReal.coe_ne_top).symm
  · rw [hyperexponentialMeasure_of_not_pos hr]
    have hf : hyperexponentialPDF p r = 0 := by
      funext x
      simp [hyperexponentialPDF, hyperexponentialPDFReal, hr]
    rw [hf, withDensity_zero]

/-- Hyperexponential laws have no atoms, including at zero. -/
instance (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    NullSingletonClass (hyperexponentialMeasure p r) := by
  rw [hyperexponentialMeasure_eq_withDensity]
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a hyperexponential law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_hyperexponentialMeasure (hX : HasLaw X (hyperexponentialMeasure p r) P) :
    HasPDF X P volume := by
  exact hasPDF_of_hasLaw_withDensity (measurable_hyperexponentialPDF p r).aemeasurable
    (by rwa [hyperexponentialMeasure_eq_withDensity] at hX)

/-- The canonical pdf agrees almost everywhere with the named hyperexponential density. -/
theorem pdf_eq_hyperexponentialPDF_of_hasLaw_hyperexponentialMeasure
    (hX : HasLaw X (hyperexponentialMeasure p r) P) :
    pdf X P volume =ᵐ[volume] hyperexponentialPDF p r := by
  exact pdf_eq_of_hasLaw_withDensity (measurable_hyperexponentialPDF p r).aemeasurable
    (by rwa [hyperexponentialMeasure_eq_withDensity] at hX)

/-- The Radon--Nikodym derivative is the named density. -/
theorem rnDeriv_hyperexponentialMeasure (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    (hyperexponentialMeasure p r).rnDeriv volume =ᵐ[volume] hyperexponentialPDF p r := by
  rw [hyperexponentialMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume
    (measurable_hyperexponentialPDF p r)

/-- The real density is positive exactly on the positive half-line for valid parameters. -/
theorem hyperexponentialPDFReal_pos_iff (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    0 < hyperexponentialPDFReal p r x ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    rw [hyperexponentialPDFReal_of_not_pos (by tauto)] at h
    exact (lt_irrefl 0) h
  · intro hx
    rw [hyperexponentialPDFReal_of_pos hr hx]
    obtain ⟨i, hi⟩ := p.support_weights_nonempty
    have hwi : 0 < p.weights i := pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    exact Finset.sum_pos' (fun j _ ↦ component_nonneg hr j x)
      ⟨i, Finset.mem_univ i,
        mul_pos (mul_pos (NNReal.coe_pos.mpr hwi) (hr i hwi)) (exp_pos _)⟩

/-- A hyperexponential variable is strictly positive almost surely. -/
theorem ae_pos_hyperexponentialMeasure (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) :
    ∀ᵐ x ∂hyperexponentialMeasure p r, 0 < x := by
  rw [hyperexponentialMeasure_eq_withDensity,
    ae_withDensity_iff (measurable_hyperexponentialPDF p r)]
  exact ae_of_all _ fun x hx ↦ by
    by_contra h
    exact hx (by simp [hyperexponentialPDF, hyperexponentialPDFReal, h])

/-- The topological support is `[0, ∞)`: its boundary point zero is not an atom. -/
@[simp]
theorem support_hyperexponentialMeasure (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    (hyperexponentialMeasure p r).support = Ici 0 := by
  rw [hyperexponentialMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_hyperexponentialPDF p r) isOpen_Ioi]
  · exact closure_Ioi (0 : ℝ)
  · ext x
    simpa only [Function.mem_support, hyperexponentialPDF, ne_eq, ENNReal.ofReal_eq_zero,
      not_le, mem_Ioi] using hyperexponentialPDFReal_pos_iff hr (x := x)

/-- The cdf is zero at nonpositive points and otherwise one minus the finite survival mixture.
The sum may include inactive components, whose summands vanish regardless of their rates. -/
theorem cdf_hyperexponentialMeasure_eq (hr : ∀ i, 0 < p.weights i → 0 < r i) (x : ℝ) :
    cdf (hyperexponentialMeasure p r) x =
      if x ≤ 0 then 0 else 1 - ∑ i, (p.weights i : ℝ) * exp (-(r i * x)) := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  have hfinite (i : ι) : ((p.weights i : ℝ≥0∞) • expMeasure (r i)) (Iic x) ≠ ∞ := by
    by_cases hi : p.weights i = 0
    · simp [hi]
    · let _ := isProbabilityMeasure_expMeasure (hr i (pos_iff_ne_zero.mpr hi))
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  rw [cdf_eq_real, measureReal_def, hyperexponentialMeasure_of_pos hr,
    Measure.finsetSum_apply, ENNReal.toReal_sum (fun i _ ↦ hfinite i)]
  have hterm (i : ι) :
      (((p.weights i : ℝ≥0∞) • expMeasure (r i)) (Iic x)).toReal =
        (p.weights i : ℝ) * (if 0 ≤ x then 1 - exp (-(r i * x)) else 0) := by
    by_cases hi : p.weights i = 0
    · simp [hi]
    · let _ := isProbabilityMeasure_expMeasure (hr i (pos_iff_ne_zero.mpr hi))
      rw [← measureReal_def, measureReal_ennreal_smul_apply, ← cdf_eq_real,
        cdf_expMeasure_eq (hr i (pos_iff_ne_zero.mpr hi))]
      rfl
  simp_rw [hterm]
  have hw : ∑ i, (p.weights i : ℝ) = 1 := by exact_mod_cast p.total_of_fintype
  by_cases hx : x ≤ 0
  · rcases lt_or_eq_of_le hx with hx | rfl
    · simp [hx.le, not_le.mpr hx]
    · simp
  · simp only [ite_eq_right hx, ite_eq_left (le_of_not_ge hx)]
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hw]

/-- Changing the rates of zero-weight components leaves the law unchanged, even at invalid
parameters. -/
theorem hyperexponentialMeasure_congr {s : ι → ℝ}
    (h : ∀ i, 0 < p.weights i → r i = s i) :
    hyperexponentialMeasure p r = hyperexponentialMeasure p s := by
  have hvalid : (∀ i, 0 < p.weights i → 0 < r i) ↔
      ∀ i, 0 < p.weights i → 0 < s i := by
    constructor <;> intro hr i hi <;> simpa only [h i hi] using hr i hi
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · rw [hyperexponentialMeasure_of_pos hr, hyperexponentialMeasure_of_pos (hvalid.mp hr)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hwi : p.weights i = 0
    · simp [hwi]
    · rw [h i (pos_iff_ne_zero.mpr hwi)]
  · rw [hyperexponentialMeasure_of_not_pos hr,
      hyperexponentialMeasure_of_not_pos (mt hvalid.mpr hr)]

/-- Equal rates recover the exponential law, for arbitrary simplex weights, including the
zero law at nonpositive rates. -/
@[simp]
theorem hyperexponentialMeasure_const (p : StdSimplex ℝ≥0 ι) (a : ℝ) :
    hyperexponentialMeasure p (fun _ ↦ a) = expMeasure a := by
  by_cases ha : 0 < a
  · rw [hyperexponentialMeasure_of_pos (fun _ _ ↦ ha), ← Finset.sum_smul]
    have hw : ∑ i, (p.weights i : ℝ≥0∞) = 1 := by exact_mod_cast p.total_of_fintype
    rw [hw, one_smul]
  · have hpdf : exponentialPDF a = 0 := by
      funext x
      rw [exponentialPDF_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero]
      split_ifs
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ha) (exp_nonneg _)
      · exact le_rfl
    have hmeasure : expMeasure a = 0 := by
      rw [expMeasure_eq_withDensity, hpdf, withDensity_zero]
    simp [hyperexponentialMeasure, hmeasure]

section Integration

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}

/-- Integrability under a hyperexponential law is equivalent to integrability under each
positive-weight exponential component. Inactive rates impose no condition. -/
theorem integrable_hyperexponentialMeasure_iff
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    Integrable f (hyperexponentialMeasure p r) ↔
      ∀ i, 0 < p.weights i → Integrable f (expMeasure (r i)) := by
  rw [hyperexponentialMeasure_of_pos hr, integrable_finsetSum_measure]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro hf i hi
    exact (integrable_smul_measure (by simpa using hi.ne') ENNReal.coe_ne_top).mp (hf i)
  · intro hf i
    by_cases hi : p.weights i = 0
    · simp [hi]
    · exact (hf i (pos_iff_ne_zero.mpr hi)).smul_measure ENNReal.coe_ne_top

variable [NormedSpace ℝ E]

/-- An integrable observable's expectation is the weighted sum of its component expectations. -/
theorem integral_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (hf : Integrable f (hyperexponentialMeasure p r)) :
    ∫ x, f x ∂hyperexponentialMeasure p r =
      ∑ i, (p.weights i : ℝ) • ∫ x, f x ∂expMeasure (r i) := by
  rw [hyperexponentialMeasure_of_pos hr] at hf ⊢
  rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hf)]
  simp only [integral_smul_measure, ENNReal.coe_toReal]

end Integration

end TauCeti.Probability
