/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Sqrt
public import TauCeti.Probability.Distributions.Affine
import TauCeti.Analysis.SpecialFunctions.Gamma

/-!
# Chi distributions

The chi law `chiMeasure k s` is the law of `s * √X` for a chi-squared variable `X` with `k`
degrees of freedom. It describes Gaussian radii, with a scale parameter independent of the
degrees of freedom. Nonnegative degrees and positive scale give probability measures. Zero
degrees give a point mass at zero; negative degrees or nonpositive scale give the zero measure.

This file supplies the measure, its Lebesgue density at positive degrees, parameter
measurability, the cumulative distribution function, and the squaring and scaling identities.
The density is written in standardized coordinates `x / s`. The change of variables reuses
`map_sqrt_chiSquaredMeasure` and `map_affine_withDensity_volume`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {k s c x : ℝ}

/-- The chi law of degree `k` and scale `s`: the image of the chi-squared law by `s * √·`
when `s > 0`, and zero otherwise. Degree zero gives a Dirac law for positive scale. -/
def chiMeasure (k s : ℝ) : Measure ℝ :=
  if 0 < s then (chiSquaredMeasure k).map (fun x ↦ s * √x) else 0

/-- The defining square-root pushforward at positive scale. -/
theorem chiMeasure_of_scale_pos (hs : 0 < s) :
    chiMeasure k s = (chiSquaredMeasure k).map (fun x ↦ s * √x) := by
  simp only [chiMeasure, ite_eq_left hs]

/-- At positive degrees and scale, the chi law is the scaled square-root image of a Gamma law. -/
theorem chiMeasure_eq_map_gammaMeasure (hk : 0 < k) (hs : 0 < s) :
    chiMeasure k s = (gammaMeasure (k / 2) (1 / 2)).map (fun x ↦ s * √x) := by
  rw [chiMeasure_of_scale_pos hs, chiSquaredMeasure_eq_gammaMeasure hk]

/-- Nonpositive scale gives the zero measure. -/
@[simp]
theorem chiMeasure_of_scale_nonpos (hs : s ≤ 0) : chiMeasure k s = 0 := by
  simp [chiMeasure, not_lt.mpr hs]

/-- Negative degrees give the zero measure at every scale. -/
@[simp]
theorem chiMeasure_of_neg (hk : k < 0) : chiMeasure k s = 0 := by
  simp [chiMeasure, chiSquaredMeasure_of_neg hk]

/-- At degree zero and positive scale, the chi law is the point mass at zero. -/
@[simp]
theorem chiMeasure_zero (hs : 0 < s) : chiMeasure 0 s = Measure.dirac 0 := by
  simp [chiMeasure_of_scale_pos hs, Measure.map_dirac]

/-- Nonnegative degrees and positive scale give a probability measure. -/
theorem isProbabilityMeasure_chiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    IsProbabilityMeasure (chiMeasure k s) := by
  rw [chiMeasure_of_scale_pos hs]
  let _ := isProbabilityMeasure_chiSquaredMeasure hk
  infer_instance

/-- The real chi density, written in standardized coordinates. It vanishes outside the positive
half-line, at degree zero, and at invalid parameters. -/
def chiPDFReal (k s x : ℝ) : ℝ :=
  if 0 < k ∧ 0 < s ∧ 0 < x then
    (2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) *
      (x / s) ^ (k - 1) * exp (-(x / s) ^ 2 / 2) / s
  else 0

/-- The extended nonnegative chi density. Degree zero is singular and has no density identity. -/
def chiPDF (k s x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (chiPDFReal k s x)

/-- The extended chi density is obtained by applying `ENNReal.ofReal` to the real density. -/
theorem chiPDF_eq_ofReal (k s x : ℝ) : chiPDF k s x = ENNReal.ofReal (chiPDFReal k s x) :=
  chiPDF.eq_def k s x

/-- The chi density on the positive half-line at positive parameters. -/
@[simp]
theorem chiPDFReal_of_pos (hk : 0 < k) (hs : 0 < s) (hx : 0 < x) :
    chiPDFReal k s x = (2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) *
      (x / s) ^ (k - 1) * exp (-(x / s) ^ 2 / 2) / s := by
  simp [chiPDFReal, hk, hs, hx]

/-- The density vanishes off the positive-parameter, positive-coordinate domain. -/
theorem chiPDFReal_of_not_pos (h : ¬ (0 < k ∧ 0 < s ∧ 0 < x)) :
    chiPDFReal k s x = 0 := by
  simp [chiPDFReal, h]

/-- The extended density vanishes off the positive-parameter, positive-coordinate domain. -/
theorem chiPDF_of_not_pos (h : ¬ (0 < k ∧ 0 < s ∧ 0 < x)) : chiPDF k s x = 0 := by
  simp [chiPDF_eq_ofReal, chiPDFReal_of_not_pos h]

/-- The real chi density vanishes on the nonpositive half-line. -/
@[simp]
theorem chiPDFReal_of_nonpos (hx : x ≤ 0) : chiPDFReal k s x = 0 :=
  chiPDFReal_of_not_pos (by grind)

/-- The extended chi density vanishes on the nonpositive half-line. -/
@[simp]
theorem chiPDF_of_nonpos (hx : x ≤ 0) : chiPDF k s x = 0 :=
  chiPDF_of_not_pos (by grind)

/-- The extended chi density on the positive half-line at positive parameters. -/
@[simp]
theorem chiPDF_of_pos (hk : 0 < k) (hs : 0 < s) (hx : 0 < x) :
    chiPDF k s x = ENNReal.ofReal ((2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) *
      (x / s) ^ (k - 1) * exp (-(x / s) ^ 2 / 2) / s) := by
  rw [chiPDF_eq_ofReal, chiPDFReal_of_pos hk hs hx]

/-- The real chi density is nonnegative for every parameter value. -/
theorem chiPDFReal_nonneg (k s x : ℝ) : 0 ≤ chiPDFReal k s x := by
  by_cases h : 0 < k ∧ 0 < s ∧ 0 < x
  · obtain ⟨hk, hs, hx⟩ := h
    rw [chiPDFReal_of_pos hk hs hx]
    positivity
  · simp [chiPDFReal_of_not_pos h]

/-- The positivity set of a valid positive-degree chi density is the positive half-line. -/
theorem chiPDFReal_pos_iff (hk : 0 < k) (hs : 0 < s) :
    0 < chiPDFReal k s x ↔ 0 < x := by
  by_cases hx : 0 < x
  · simp [chiPDFReal_of_pos hk hs hx, hx,
      show 0 < (2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) *
        (x / s) ^ (k - 1) * exp (-(x / s) ^ 2 / 2) / s by positivity]
  · simp [chiPDFReal, hx]

/-- The extended density has the stated real density as its real value. -/
@[simp]
theorem toReal_chiPDF (k s x : ℝ) : (chiPDF k s x).toReal = chiPDFReal k s x := by
  exact ENNReal.toReal_ofReal (chiPDFReal_nonneg k s x)

/-- The chi density is jointly measurable in degrees, scale, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_chiPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ chiPDFReal p.1.1 p.1.2 p.2 := by
  unfold chiPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The real chi density is measurable in its coordinate. -/
@[fun_prop]
theorem measurable_chiPDFReal (k s : ℝ) : Measurable (chiPDFReal k s) := by
  exact measurable_uncurry_chiPDFReal.comp
    (show Measurable fun x : ℝ ↦ ((k, s), x) by fun_prop)

/-- The extended chi density is jointly measurable in degrees, scale, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_chiPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ chiPDF p.1.1 p.1.2 p.2 := by
  unfold chiPDF
  fun_prop

/-- The chi density is measurable in its coordinate. -/
@[fun_prop]
theorem measurable_chiPDF (k s : ℝ) : Measurable (chiPDF k s) := by
  exact measurable_uncurry_chiPDF.comp (show Measurable fun x : ℝ ↦ ((k, s), x) by fun_prop)

/-- At positive degrees and scale the chi law has its named Lebesgue density. -/
theorem chiMeasure_eq_withDensity (hk : 0 < k) (hs : 0 < s) :
    chiMeasure k s = volume.withDensity (chiPDF k s) := by
  have hstandard : (chiSquaredMeasure k).map Real.sqrt =
      volume.withDensity (chiPDF k 1) := by
    rw [map_sqrt_chiSquaredMeasure hk, ← withDensity_indicator measurableSet_Ioi]
    apply withDensity_congr_ae
    refine .of_forall fun x ↦ ?_
    by_cases hx : 0 < x
    · simp [hx, chiPDF_of_pos hk zero_lt_one hx]
    · simp [hx, chiPDF_of_nonpos (le_of_not_gt hx)]
  have hpush : (chiSquaredMeasure k).map (fun x ↦ s * √x) =
      ((chiSquaredMeasure k).map Real.sqrt).map (fun x ↦ s * x) := by
    exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
  rw [chiMeasure_of_scale_pos hs, hpush, hstandard]
  have hmap := map_affine_withDensity_volume (a := 0) (b := s)
    (chiPDF k 1) hs.ne'
  simp only [zero_add] at hmap
  rw [hmap]
  apply withDensity_congr_ae
  refine .of_forall fun x ↦ ?_
  simp only [affineDensity_apply, abs_of_pos hs, sub_zero]
  by_cases hx : 0 < x
  · rw [chiPDF_of_pos hk zero_lt_one (div_pos hx hs), chiPDF_of_pos hk hs hx]
    simp only [div_one]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · rw [chiPDF_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) hs.le),
      chiPDF_of_nonpos (le_of_not_gt hx)]
    simp

/-- The chi family is jointly Giry measurable, including its invalid and Dirac branches. -/
@[fun_prop]
theorem measurable_chiMeasure : Measurable fun p : ℝ × ℝ ↦ chiMeasure p.1 p.2 := by
  have h : (fun p : ℝ × ℝ ↦ chiMeasure p.1 p.2) = fun p ↦
      if 0 < p.2 then
        if p.1 = 0 then Measure.dirac 0 else volume.withDensity (chiPDF p.1 p.2)
      else 0 := by
    funext p
    by_cases hs : 0 < p.2
    · by_cases hk : p.1 = 0
      · simp [hs, hk, chiMeasure_zero hs]
      · by_cases hk' : 0 < p.1
        · simp [hs, hk, chiMeasure_eq_withDensity hk' hs]
        · simp only [ite_eq_left hs, ite_eq_right hk,
            chiMeasure_of_neg (lt_of_le_of_ne (le_of_not_gt hk') hk)]
          have hz : chiPDF p.1 p.2 = 0 := by
            funext x
            exact chiPDF_of_not_pos (by tauto)
          rw [hz]
          simp
    · simp [hs, chiMeasure_of_scale_nonpos (le_of_not_gt hs)]
  rw [h]
  refine Measurable.ite (by measurability) (Measurable.ite (by measurability) measurable_const ?_)
    measurable_const
  exact measurable_withDensity measurable_uncurry_chiPDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a positive-degree chi law has a density. -/
theorem hasPDF_of_hasLaw_chiMeasure (hk : 0 < k) (hs : 0 < s)
    (hX : HasLaw X (chiMeasure k s) P) : HasPDF X P := by
  rw [chiMeasure_eq_withDensity hk hs] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_chiPDF k s).aemeasurable hX

/-- The canonical density of a chi variable agrees almost everywhere with `chiPDF`. -/
theorem pdf_eq_chiPDF_of_hasLaw_chiMeasure (hk : 0 < k) (hs : 0 < s)
    (hX : HasLaw X (chiMeasure k s) P) : pdf X P =ᵐ[volume] chiPDF k s := by
  rw [chiMeasure_eq_withDensity hk hs] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_chiPDF k s).aemeasurable hX

/-- The Radon–Nikodym derivative of a positive-degree chi law is its named density. -/
theorem rnDeriv_chiMeasure (hk : 0 < k) (hs : 0 < s) :
    (chiMeasure k s).rnDeriv volume =ᵐ[volume] chiPDF k s := by
  rw [chiMeasure_eq_withDensity hk hs]
  exact Measure.rnDeriv_withDensity _ (measurable_chiPDF k s)

/-- Positive-degree chi laws are carried by the positive half-line. -/
theorem ae_pos_chiMeasure (hk : 0 < k) :
    ∀ᵐ x ∂chiMeasure k s, 0 < x := by
  by_cases hs : 0 < s
  swap
  · simp [chiMeasure_of_scale_nonpos (le_of_not_gt hs)]
  rw [chiMeasure_eq_map_gammaMeasure hk hs]
  apply (ae_map_iff (by fun_prop) measurableSet_Ioi).2
  filter_upwards [ae_pos_gammaMeasure (k / 2) (1 / 2)] with x hx
  exact mul_pos hs (Real.sqrt_pos.2 hx)

/-- Positive scaling multiplies the chi scale in every parameter regime. -/
@[simp]
theorem chiMeasure_map_const_mul (hc : 0 < c) :
    (chiMeasure k s).map (fun x ↦ c * x) = chiMeasure k (c * s) := by
  by_cases hs : 0 < s
  swap
  · simp [chiMeasure_of_scale_nonpos (le_of_not_gt hs),
      chiMeasure_of_scale_nonpos (mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hs))]
  rw [chiMeasure_of_scale_pos hs, chiMeasure_of_scale_pos (mul_pos hc hs),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  exact (mul_assoc c s (√x)).symm

/-- Taking a scaled square root of a chi-squared variable gives the chi law. -/
theorem hasLaw_chiMeasure_of_hasLaw_chiSquaredMeasure (hs : 0 < s)
    (hX : HasLaw X (chiSquaredMeasure k) P) :
    HasLaw (fun ω ↦ s * √(X ω)) (chiMeasure k s) P := by
  rw [chiMeasure_of_scale_pos hs]
  exact (hasLaw_map (X := fun x : ℝ ↦ s * √x) (by fun_prop)).fun_comp hX

/-- Squaring a chi variable gives the squared scale times a chi-squared variable. -/
theorem chiMeasure_map_sq (hs : 0 < s) :
    (chiMeasure k s).map (fun x ↦ x ^ 2) =
      (chiSquaredMeasure k).map (fun x ↦ s ^ 2 * x) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [chiMeasure_of_neg hk, chiSquaredMeasure_of_neg hk]
  · simp [chiMeasure_zero hs, Measure.map_dirac]
  · rw [chiMeasure_eq_map_gammaMeasure hk hs, chiSquaredMeasure_eq_gammaMeasure hk,
      Measure.map_map (by fun_prop) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [ae_pos_gammaMeasure (k / 2) (1 / 2)] with x hx
    simp [mul_pow, Real.sq_sqrt hx.le]

/-- The chi cdf is the regularized lower incomplete Gamma function on the nonnegative half-line
and zero below it. -/
@[simp]
theorem cdf_chiMeasure_eq (hk : 0 < k) (hs : 0 < s) (x : ℝ) :
    cdf (chiMeasure k s) x =
      if x < 0 then 0 else regularizedGamma (k / 2) ((x / s) ^ 2 / 2) := by
  have := isProbabilityMeasure_chiSquaredMeasure hk.le
  rw [chiMeasure_of_scale_pos hs, Measure.cdf_map_const_mul_sqrt _ hs, cdf_chiSquaredMeasure_eq hk]

/-- The cdf at the degree-zero boundary is the unit step at zero. -/
theorem cdf_chiMeasure_zero (hs : 0 < s) (x : ℝ) :
    cdf (chiMeasure 0 s) x = if 0 ≤ x then 1 else 0 := by
  rw [chiMeasure_zero hs, cdf_dirac]

end TauCeti.Probability
