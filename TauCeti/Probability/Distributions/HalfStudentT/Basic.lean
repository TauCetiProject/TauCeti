/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.Basic
public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.BetaPrime.Basic
import TauCeti.Probability.Distributions.Cauchy.Affine
import TauCeti.Probability.Distributions.StudentT.ChiSquared

/-!
# Half-Student t and half-Cauchy distributions

The half-Student t law of degree `ν` and scale `s` is the law of `s * |T|` for a Student t
variable `T`. Positive degrees and scale give a probability law; other parameters give zero.
Degree one is the half-Cauchy law. These distributions model positive magnitudes with polynomial
tails.

This file constructs the laws, identifies their Lebesgue densities, proves joint parameter
measurability, and establishes their almost-sure positivity, topological support, and scaling law.
The density is twice the scaled Student t density on the positive half-line. Folding and affine
change of variables supply the density identity.
The square-root beta-prime representation transfers sharp real-power moments to this law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 28.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ν s c x : ℝ}

/-- The law of `s * |T|` for `T` with Student t law of degree `ν`, when both parameters are
positive. Invalid parameters give the zero measure. -/
def halfStudentTMeasure (ν s : ℝ) : Measure ℝ :=
  if 0 < ν ∧ 0 < s then (studentTMeasure ν).map (fun x ↦ s * |x|) else 0

/-- The defining folded and scaled Student t construction at valid parameters. -/
theorem halfStudentTMeasure_of_pos (hν : 0 < ν) (hs : 0 < s) :
    halfStudentTMeasure ν s = (studentTMeasure ν).map (fun x ↦ s * |x|) := by
  simp [halfStudentTMeasure, hν, hs]

/-- A half-Student t law is the scaled square-root image of a beta-prime law with shapes
`1 / 2` and `ν / 2`. -/
theorem halfStudentTMeasure_eq_map_betaPrimeMeasure (hν : 0 < ν) (hs : 0 < s) :
    halfStudentTMeasure ν s =
      (betaPrimeMeasure (1 / 2) (ν / 2)).map (fun x ↦ s * √(ν * x)) := by
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure one_half_pos (half_pos hν)]
  norm_num only [mul_one_div, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  have hdegrees : 2 * (ν / 2) = ν := by ring
  rw [hdegrees, ← studentTMeasure_map_sq hν,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), halfStudentTMeasure_of_pos hν hs]
  congr 1
  ext x
  simp only [Function.comp_apply]
  have hcancel : ν * (1 / 2 / (ν / 2) * x ^ 2) = x ^ 2 := by
    field_simp
  rw [hcancel, sqrt_sq_eq_abs]

/-- Invalid degrees or scale give zero measure. -/
@[simp]
theorem halfStudentTMeasure_of_not_pos (h : ¬ (0 < ν ∧ 0 < s)) :
    halfStudentTMeasure ν s = 0 := by
  simp only [halfStudentTMeasure, ite_eq_right h]

/-- Positive degrees and scale give a probability measure. -/
theorem isProbabilityMeasure_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    IsProbabilityMeasure (halfStudentTMeasure ν s) := by
  rw [halfStudentTMeasure_of_pos hν hs]
  let _ := isProbabilityMeasure_studentTMeasure hν
  infer_instance

/-- The real half-Student t density, zero off the positive half-line and at invalid parameters. -/
def halfStudentTPDFReal (ν s x : ℝ) : ℝ :=
  if 0 < ν ∧ 0 < s ∧ 0 < x then 2 * studentTPDFReal ν (x / s) / s else 0

/-- The extended nonnegative half-Student t density. -/
def halfStudentTPDF (ν s x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (halfStudentTPDFReal ν s x)

/-- The density on the positive half-line at valid parameters. -/
@[simp]
theorem halfStudentTPDFReal_of_pos (hν : 0 < ν) (hs : 0 < s) (hx : 0 < x) :
    halfStudentTPDFReal ν s x = 2 * studentTPDFReal ν (x / s) / s := by
  simp [halfStudentTPDFReal, hν, hs, hx]

/-- The density vanishes outside its positive-parameter, positive-coordinate domain. -/
@[simp]
theorem halfStudentTPDFReal_of_not_pos (h : ¬ (0 < ν ∧ 0 < s ∧ 0 < x)) :
    halfStudentTPDFReal ν s x = 0 := by
  simp only [halfStudentTPDFReal, ite_eq_right h]

/-- The half-Student t density is nonnegative. -/
theorem halfStudentTPDFReal_nonneg (ν s x : ℝ) : 0 ≤ halfStudentTPDFReal ν s x := by
  by_cases h : 0 < ν ∧ 0 < s ∧ 0 < x
  · rw [halfStudentTPDFReal_of_pos h.1 h.2.1 h.2.2]
    exact div_nonneg (mul_nonneg (by norm_num) (studentTPDFReal_nonneg _ _)) h.2.1.le
  · simp [h]

/-- For valid parameters the density is positive exactly on the positive half-line. -/
theorem halfStudentTPDFReal_pos_iff (hν : 0 < ν) (hs : 0 < s) :
    0 < halfStudentTPDFReal ν s x ↔ 0 < x := by
  by_cases hx : 0 < x
  · rw [halfStudentTPDFReal_of_pos hν hs hx]
    exact iff_of_true (div_pos (mul_pos two_pos (studentTPDFReal_pos hν _)) hs) hx
  · simp [halfStudentTPDFReal, hx]

/-- The extended density is obtained from its real companion by `ENNReal.ofReal`. -/
theorem halfStudentTPDF_eq_ofReal (ν s x : ℝ) :
    halfStudentTPDF ν s x = ENNReal.ofReal (halfStudentTPDFReal ν s x) := (rfl)

/-- The extended density on the positive half-line at valid parameters. -/
@[simp]
theorem halfStudentTPDF_of_pos (hν : 0 < ν) (hs : 0 < s) (hx : 0 < x) :
    halfStudentTPDF ν s x = ENNReal.ofReal (2 * studentTPDFReal ν (x / s) / s) := by
  rw [halfStudentTPDF_eq_ofReal, halfStudentTPDFReal_of_pos hν hs hx]

/-- The extended density vanishes outside the valid positive-coordinate domain. -/
@[simp]
theorem halfStudentTPDF_of_not_pos (h : ¬ (0 < ν ∧ 0 < s ∧ 0 < x)) :
    halfStudentTPDF ν s x = 0 := by
  rw [halfStudentTPDF_eq_ofReal, halfStudentTPDFReal_of_not_pos h, ENNReal.ofReal_zero]

@[simp]
theorem toReal_halfStudentTPDF (ν s x : ℝ) :
    (halfStudentTPDF ν s x).toReal = halfStudentTPDFReal ν s x := by
  exact ENNReal.toReal_ofReal (halfStudentTPDFReal_nonneg ν s x)

/-- The real density is jointly measurable in degrees, scale, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_halfStudentTPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ halfStudentTPDFReal p.1.1 p.1.2 p.2 := by
  unfold halfStudentTPDFReal
  have hstudent : Measurable fun p : (ℝ × ℝ) × ℝ ↦
      studentTPDFReal p.1.1 (p.2 / p.1.2) := by
    have h := measurable_uncurry_studentTPDF.comp
      (by fun_prop : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ (p.1.1, p.2 / p.1.2)))
    simpa only [Function.comp_apply, toReal_studentTPDF] using h.ennreal_toReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The extended density is jointly measurable. -/
@[fun_prop]
theorem measurable_uncurry_halfStudentTPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ halfStudentTPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_halfStudentTPDFReal.ennreal_ofReal

/-- The extended density is measurable in the sample coordinate. -/
@[fun_prop]
theorem measurable_halfStudentTPDF (ν s : ℝ) : Measurable (halfStudentTPDF ν s) :=
  measurable_uncurry_halfStudentTPDF.comp (by fun_prop : Measurable fun x : ℝ ↦ ((ν, s), x))

/-- Folding first and then scaling gives the half-Student t law. -/
theorem halfStudentTMeasure_eq_map_abs (hν : 0 < ν) (hs : 0 < s) :
    halfStudentTMeasure ν s = ((studentTMeasure ν).map (|·|)).map (fun x ↦ s * x) := by
  rw [halfStudentTMeasure_of_pos hν hs, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The folded and scaled law has the named Lebesgue density, for every parameter value. -/
theorem halfStudentTMeasure_eq_withDensity (ν s : ℝ) :
    halfStudentTMeasure ν s = volume.withDensity (halfStudentTPDF ν s) := by
  by_cases h : 0 < ν ∧ 0 < s
  · have hscale := map_affine_withDensity_volume (a := 0) (b := s)
      ((Ioi 0).indicator fun x ↦ studentTPDF ν x + studentTPDF ν (-x)) h.2.ne'
    simp only [zero_add] at hscale
    rw [halfStudentTMeasure_eq_map_abs h.1 h.2, studentTMeasure_def,
      map_abs_withDensity (measurable_studentTPDF ν), hscale]
    apply withDensity_congr_ae
    refine .of_forall fun x ↦ ?_
    simp only [affineDensity_apply, abs_of_pos h.2, sub_zero]
    by_cases hx : 0 < x
    · simp only [indicator_of_mem (mem_Ioi.mpr (div_pos hx h.2)),
        halfStudentTPDF_eq_ofReal, halfStudentTPDFReal_of_pos h.1 h.2 hx,
        studentTPDF_eq_ofReal, studentTPDFReal_neg]
      rw [← ENNReal.ofReal_add (studentTPDFReal_nonneg _ _) (studentTPDFReal_nonneg _ _),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr h.2.le)]
      congr 1
      ring
    · rw [indicator_of_notMem (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
        (le_of_not_gt hx) h.2.le)), mul_zero, halfStudentTPDF_eq_ofReal,
        halfStudentTPDFReal_of_not_pos (by tauto), ENNReal.ofReal_zero]
  · rw [halfStudentTMeasure_of_not_pos h]
    have hz : halfStudentTPDF ν s = 0 := by
      ext x
      rw [halfStudentTPDF_eq_ofReal, halfStudentTPDFReal_of_not_pos (by tauto)]
      simp
    rw [hz, withDensity_zero]

/-- The half-Student t family is jointly Giry measurable, including invalid parameters. -/
@[fun_prop]
theorem measurable_halfStudentTMeasure :
    Measurable fun p : ℝ × ℝ ↦ halfStudentTMeasure p.1 p.2 := by
  simp_rw [halfStudentTMeasure_eq_withDensity]
  exact measurable_withDensity measurable_uncurry_halfStudentTPDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℝ}

/-- Folding and positively scaling a Student t variable gives the half-Student t law. -/
theorem hasLaw_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s)
    (hT : HasLaw T (studentTMeasure ν) P) :
    HasLaw (fun ω ↦ s * |T ω|) (halfStudentTMeasure ν s) P := by
  rw [halfStudentTMeasure_of_pos hν hs]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ ↦ s * |x|).aemeasurable).comp hT

/-- Every variable with a half-Student t law admits a Lebesgue density. -/
theorem hasPDF_of_hasLaw_halfStudentTMeasure
    (hT : HasLaw T (halfStudentTMeasure ν s) P) : HasPDF T P := by
  rw [halfStudentTMeasure_eq_withDensity] at hT
  exact hasPDF_of_hasLaw_withDensity (measurable_halfStudentTPDF ν s).aemeasurable hT

/-- The canonical density is the named half-Student t density almost everywhere. -/
theorem pdf_eq_halfStudentTPDF_of_hasLaw_halfStudentTMeasure
    (hT : HasLaw T (halfStudentTMeasure ν s) P) :
    pdf T P volume =ᵐ[volume] halfStudentTPDF ν s := by
  rw [halfStudentTMeasure_eq_withDensity] at hT
  exact pdf_eq_of_hasLaw_withDensity (measurable_halfStudentTPDF ν s).aemeasurable hT

/-- The Radon--Nikodym derivative of a half-Student t law is its density. -/
theorem rnDeriv_halfStudentTMeasure (ν s : ℝ) :
    (halfStudentTMeasure ν s).rnDeriv volume =ᵐ[volume] halfStudentTPDF ν s := by
  rw [halfStudentTMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_halfStudentTPDF ν s)

/-- Half-Student t laws are atomless, also on the invalid zero-measure branch. -/
instance nullSingletonClass_halfStudentTMeasure (ν s : ℝ) :
    NullSingletonClass (halfStudentTMeasure ν s) := by
  rw [halfStudentTMeasure_eq_withDensity]
  infer_instance

/-- For positive parameters the topological support is the closed nonnegative half-line. -/
@[simp]
theorem support_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    (halfStudentTMeasure ν s).support = Ici 0 := by
  rw [halfStudentTMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_halfStudentTPDF ν s) isOpen_Ioi,
    closure_Ioi]
  ext x
  rw [Function.mem_support, halfStudentTPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff,
    halfStudentTPDFReal_pos_iff hν hs, mem_Ioi]

/-- The half-Student t variable is positive almost surely, despite zero belonging to its
topological support. -/
theorem ae_pos_halfStudentTMeasure (ν s : ℝ) :
    ∀ᵐ x ∂halfStudentTMeasure ν s, 0 < x := by
  rw [halfStudentTMeasure_eq_withDensity]
  rw [ae_withDensity_iff (measurable_halfStudentTPDF ν s)]
  exact .of_forall fun x hx ↦ by
    by_contra h
    exact hx (by simp [halfStudentTPDF, halfStudentTPDFReal, h])

/-- Multiplying by a positive constant multiplies the half-Student t scale. -/
theorem halfStudentTMeasure_map_const_mul (hc : 0 < c) :
    (halfStudentTMeasure ν s).map (fun x ↦ c * x) = halfStudentTMeasure ν (c * s) := by
  by_cases h : 0 < ν ∧ 0 < s
  · rw [halfStudentTMeasure_of_pos h.1 h.2,
      halfStudentTMeasure_of_pos h.1 (mul_pos hc h.2),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x
    simp only [Function.comp_apply, mul_assoc]
  · rw [halfStudentTMeasure_of_not_pos h,
      halfStudentTMeasure_of_not_pos (by simpa [mul_pos_iff_of_pos_left hc] using h),
      Measure.map_zero]

/-- Multiplying a half-Student t variable by a positive constant multiplies its scale,
including on the invalid zero-measure branch. -/
theorem hasLaw_mul_halfStudentTMeasure (hc : 0 < c)
    (hT : HasLaw T (halfStudentTMeasure ν s) P) :
    HasLaw (fun ω ↦ c * T ω) (halfStudentTMeasure ν (c * s)) P := by
  rw [← halfStudentTMeasure_map_const_mul hc]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ ↦ c * x).aemeasurable).comp hT

/-- The half-Cauchy law is the degree-one half-Student t law. -/
abbrev halfCauchyMeasure (s : ℝ) : Measure ℝ := halfStudentTMeasure 1 s

/-- At positive scale, the half-Cauchy law is the scaled absolute value of a standard Cauchy. -/
theorem halfCauchyMeasure_eq_map_cauchyMeasure (hs : 0 < s) :
    halfCauchyMeasure s = (cauchyMeasure 0 1).map (fun x ↦ s * |x|) := by
  rw [halfCauchyMeasure, halfStudentTMeasure_of_pos one_pos hs, studentTMeasure_one]

/-- Folding a centered Cauchy law of positive scale gives the half-Cauchy law of that scale. -/
theorem cauchyMeasure_map_abs {s : ℝ≥0} (hs : 0 < s) :
    (cauchyMeasure 0 s).map (|·|) = halfCauchyMeasure s := by
  have hscale : (cauchyMeasure 0 1).map (fun x : ℝ ↦ (s : ℝ) * x) =
      cauchyMeasure 0 s := by
    have hnorm : ‖(s : ℝ)‖₊ = s := NNReal.coe_injective (by simp)
    simpa only [zero_add, mul_zero, mul_one, hnorm] using
      cauchyMeasure_map_affine 0 1 0 s
  rw [← hscale, Measure.map_map (by fun_prop) (by fun_prop),
    halfCauchyMeasure_eq_map_cauchyMeasure (by exact_mod_cast hs)]
  congr 1
  ext x
  simp only [Function.comp_apply, abs_mul, abs_of_nonneg s.coe_nonneg]

/-- The absolute value of a centered Cauchy variable of positive scale has the half-Cauchy law. -/
theorem hasLaw_halfCauchyMeasure {s : ℝ≥0} (hs : 0 < s)
    (hT : HasLaw T (cauchyMeasure 0 s) P) :
    HasLaw (fun ω ↦ |T ω|) (halfCauchyMeasure s) P := by
  rw [← cauchyMeasure_map_abs hs]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ ↦ |x|).aemeasurable).comp hT

end TauCeti.Probability
