/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.Cdf
import TauCeti.Probability.Distributions.Affine

/-!
# The beta-prime distribution

For positive shape parameters `a` and `b`, the beta-prime law is the image of a Beta `(a, b)`
law under the odds map `u ↦ u / (1 - u)`.  This file defines the law, proves its density and
cumulative distribution function, and relates it to a rescaled Fisher--Snedecor law.  The
rescaling lets the density calculation reuse the existing beta-to-F change of variables.

## Main definitions

* `TauCeti.Probability.betaPrimeMeasure` — the beta-prime probability law;
* `TauCeti.Probability.betaPrimePDFReal` and `TauCeti.Probability.betaPrimePDF` — its densities.

## Main results

* `TauCeti.Probability.betaPrimeMeasure_eq_map` — the defining Beta pushforward;
* `TauCeti.Probability.betaPrimeMeasure_eq_map_fisherSnedecorMeasure` — the rescaled F-law
  representation;
* `TauCeti.Probability.betaPrimeMeasure_eq_withDensity` — the Lebesgue-density representation;
* `TauCeti.Probability.cdf_betaPrimeMeasure_eq` — the regularized-incomplete-Beta cdf.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {a b x : ℝ}

/-- The beta-prime law with shape parameters `a` and `b`.  It is zero unless both parameters are
positive. -/
def betaPrimeMeasure (a b : ℝ) : Measure ℝ :=
  if 0 < a ∧ 0 < b then (betaMeasure a b).map (fisherSnedecorMap 2 2) else 0

/-- At positive parameters, the beta-prime law is the odds-map image of a Beta law. -/
theorem betaPrimeMeasure_eq_map (ha : 0 < a) (hb : 0 < b) :
    betaPrimeMeasure a b = (betaMeasure a b).map (fisherSnedecorMap 2 2) := by
  simp [betaPrimeMeasure, ha, hb]

/-- At invalid parameters, the beta-prime law is zero. -/
@[simp]
theorem betaPrimeMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) : betaPrimeMeasure a b = 0 := by
  simp [betaPrimeMeasure, h]

/-- The beta-prime law is a probability measure at positive parameters. -/
theorem isProbabilityMeasure_betaPrimeMeasure (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaPrimeMeasure a b) := by
  rw [betaPrimeMeasure_eq_map ha hb]
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  infer_instance

/-- The beta-prime law is a probability measure exactly at positive parameters. -/
@[simp]
theorem isProbabilityMeasure_betaPrimeMeasure_iff :
    IsProbabilityMeasure (betaPrimeMeasure a b) ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    by_contra hab
    rw [betaPrimeMeasure_of_not_pos hab] at h
    let _ : IsProbabilityMeasure (0 : Measure ℝ) := h
    exact (IsProbabilityMeasure.ne_zero (0 : Measure ℝ)) rfl
  · rintro ⟨ha, hb⟩
    exact isProbabilityMeasure_betaPrimeMeasure ha hb

/-- A beta-prime law is the positive rescaling by `a / b` of an F law with degrees `2a, 2b`. -/
theorem betaPrimeMeasure_eq_map_fisherSnedecorMeasure (ha : 0 < a) (hb : 0 < b) :
    betaPrimeMeasure a b =
      (fisherSnedecorMeasure (2 * a) (2 * b)).map (fun y ↦ (a / b) * y) := by
  have ha2 : 2 * a / 2 = a := by ring
  have hb2 : 2 * b / 2 = b := by ring
  rw [betaPrimeMeasure_eq_map ha hb,
    fisherSnedecorMeasure_eq_map (mul_pos (by norm_num) ha) (mul_pos (by norm_num) hb),
    ha2, hb2, Measure.map_map (by fun_prop) (measurable_fisherSnedecorMap (2 * a) (2 * b))]
  congr 1
  funext u
  simp only [Function.comp_apply, fisherSnedecorMap_def]
  norm_num
  have hscale : a / b * (2 * b / (2 * a)) = 1 := by
    field_simp [ha.ne', hb.ne']
  symm
  calc
    a / b * ((2 * b / (2 * a)) * u / (1 - u)) =
        (a / b * (2 * b / (2 * a))) * (u / (1 - u)) := by ring
    _ = u / (1 - u) := by rw [hscale, one_mul]

/-- A beta-prime law is almost surely positive, including vacuously at invalid parameters. -/
theorem ae_mem_Ioi_betaPrimeMeasure (a b : ℝ) :
    ∀ᵐ x ∂betaPrimeMeasure a b, x ∈ Ioi 0 := by
  by_cases h : 0 < a ∧ 0 < b
  · rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure h.1 h.2, ae_map_iff
      (by fun_prop : AEMeasurable (fun y : ℝ ↦ (a / b) * y)
        (fisherSnedecorMeasure (2 * a) (2 * b))) (by measurability)]
    filter_upwards [ae_mem_Ioi_fisherSnedecorMeasure (2 * a) (2 * b)] with y hy
    exact mul_pos (div_pos h.1 h.2) hy
  · rw [betaPrimeMeasure_of_not_pos h]
    simp

/-! ### Density -/

/-- The real-valued beta-prime density. -/
def betaPrimePDFReal (a b x : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b ∧ 0 < x then
    x ^ (a - 1) * (1 + x) ^ (-a - b) / beta a b
  else 0

/-- The extended-nonnegative-valued beta-prime density. -/
def betaPrimePDF (a b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (betaPrimePDFReal a b x)

/-- The beta-prime density is the nonnegative coercion of its real-valued version. -/
theorem betaPrimePDF_eq_ofReal (a b x : ℝ) :
    betaPrimePDF a b x = ENNReal.ofReal (betaPrimePDFReal a b x) := (rfl)

/-- At valid parameters and a positive sample point, the real beta-prime density has its
classical formula. -/
@[simp]
theorem betaPrimePDFReal_of_pos (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    betaPrimePDFReal a b x = x ^ (a - 1) * (1 + x) ^ (-a - b) / beta a b := by
  rw [betaPrimePDFReal, ite_eq_left ⟨ha, hb, hx⟩]

/-- The real beta-prime density vanishes on the nonpositive half-line. -/
@[simp]
theorem betaPrimePDFReal_of_nonpos (hx : x ≤ 0) (a b : ℝ) : betaPrimePDFReal a b x = 0 := by
  rw [betaPrimePDFReal, ite_eq_right]
  exact fun h ↦ (not_lt.mpr hx) h.2.2

/-- The real beta-prime density vanishes unless both shape parameters are positive. -/
@[simp]
theorem betaPrimePDFReal_of_not_pos (h : ¬ (0 < a ∧ 0 < b)) (x : ℝ) :
    betaPrimePDFReal a b x = 0 := by
  rw [betaPrimePDFReal, ite_eq_right]
  exact fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The beta-prime density is nonnegative. -/
theorem betaPrimePDFReal_nonneg (a b x : ℝ) : 0 ≤ betaPrimePDFReal a b x := by
  rw [betaPrimePDFReal]
  split_ifs with h
  · exact div_nonneg (mul_nonneg (Real.rpow_nonneg h.2.2.le _)
      (Real.rpow_nonneg (by linarith [h.2.2] : 0 ≤ 1 + x) _)) (beta_pos h.1 h.2.1).le
  · exact le_rfl

/-- Converting the beta-prime density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_betaPrimePDF (a b x : ℝ) :
    (betaPrimePDF a b x).toReal = betaPrimePDFReal a b x :=
  ENNReal.toReal_ofReal (betaPrimePDFReal_nonneg a b x)

/-- The real beta-prime density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_betaPrimePDFReal (a b : ℝ) : Measurable (betaPrimePDFReal a b) := by
  unfold betaPrimePDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The beta-prime density is measurable in its sample point. -/
@[fun_prop]
theorem measurable_betaPrimePDF (a b : ℝ) : Measurable (betaPrimePDF a b) :=
  (measurable_betaPrimePDFReal a b).ennreal_ofReal

private theorem affineDensity_fisherSnedecor_eq_betaPrime (ha : 0 < a) (hb : 0 < b) :
    affineDensity 0 (a / b) (fisherSnedecorPDF (2 * a) (2 * b)) = betaPrimePDF a b := by
  funext x
  rw [affineDensity_apply, betaPrimePDF, fisherSnedecorPDF_eq_ofReal]
  by_cases hx : 0 < x
  · rw [betaPrimePDFReal, ite_eq_left ⟨ha, hb, hx⟩, ← ENNReal.ofReal_mul (inv_nonneg.mpr
      (abs_nonneg (a / b)))]
    congr 1
    rw [abs_of_pos (div_pos ha hb), inv_div, sub_zero,
      fisherSnedecorPDFReal_eq_scaled_beta (mul_pos (by norm_num) ha)
        (mul_pos (by norm_num) hb) (div_pos hx (div_pos ha hb))]
    have hab : 2 * a / (2 * b) = a / b := by ring
    have harg : 2 * a * (x / (a / b)) / (2 * b) = x := by
      field_simp [ha.ne', hb.ne']
    rw [hab, harg]
    have hsum : (2 * a + 2 * b) / 2 = a + b := by ring
    rw [hsum]
    field_simp [ha.ne', hb.ne']
    ring_nf
  · have hx' : x ≤ 0 := not_lt.mp hx
    rw [betaPrimePDFReal, ite_eq_right (fun h ↦ hx h.2.2), ENNReal.ofReal_zero, sub_zero,
      fisherSnedecorPDFReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx'
        (div_pos ha hb).le), ENNReal.ofReal_zero, mul_zero]

/-- The beta-prime law has its classical density with respect to Lebesgue measure. -/
theorem betaPrimeMeasure_eq_withDensity (a b : ℝ) :
    betaPrimeMeasure a b = volume.withDensity (betaPrimePDF a b) := by
  by_cases h : 0 < a ∧ 0 < b
  · -- `map_affine_withDensity_volume` expects the scaling map in affine form.
    rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure h.1 h.2,
      fisherSnedecorMeasure_eq_withDensity,
      show (fun y : ℝ ↦ a / b * y) = fun y ↦ 0 + (a / b) * y by ext; simp,
      map_affine_withDensity_volume _ (div_ne_zero h.1.ne' h.2.ne'),
      affineDensity_fisherSnedecor_eq_betaPrime h.1 h.2]
  · rw [betaPrimeMeasure_of_not_pos h]
    have hpdf : betaPrimePDF a b = 0 := by
      funext x
      rw [betaPrimePDF, betaPrimePDFReal, ite_eq_right]
      · simp
      · exact fun hx ↦ h ⟨hx.1, hx.2.1⟩
    rw [hpdf]
    simp

section DensityCorollaries

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {X : Omega → ℝ}

/-- A random variable with a beta-prime law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_betaPrimeMeasure (hX : HasLaw X (betaPrimeMeasure a b) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_betaPrimePDF a b).aemeasurable
    (by rwa [betaPrimeMeasure_eq_withDensity a b] at hX)

/-- The density of a random variable with a beta-prime law is `betaPrimePDF`. -/
theorem pdf_eq_betaPrimePDF_of_hasLaw_betaPrimeMeasure
    (hX : HasLaw X (betaPrimeMeasure a b) P) :
    pdf X P volume =ᵐ[volume] betaPrimePDF a b :=
  pdf_eq_of_hasLaw_withDensity (measurable_betaPrimePDF a b).aemeasurable
    (by rwa [betaPrimeMeasure_eq_withDensity a b] at hX)

end DensityCorollaries

/-- The Radon–Nikodym derivative of a beta-prime law with respect to Lebesgue measure. -/
theorem rnDeriv_betaPrimeMeasure (a b : ℝ) :
    (betaPrimeMeasure a b).rnDeriv volume =ᵐ[volume] betaPrimePDF a b := by
  rw [betaPrimeMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_betaPrimePDF a b)

/-! ### Cumulative distribution function -/

/-- For positive shapes, the beta-prime cdf is zero on the nonpositive half-line and otherwise
is the regularized incomplete Beta function at `x / (1 + x)`. -/
theorem cdf_betaPrimeMeasure_eq (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    cdf (betaPrimeMeasure a b) x =
      if x ≤ 0 then 0 else regularizedIncompleteBeta a b (x / (1 + x)) := by
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure ha hb]
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure (2 * a) (2 * b)) :=
    isProbabilityMeasure_fisherSnedecorMeasure (mul_pos (by norm_num) ha)
      (mul_pos (by norm_num) hb)
  -- `cdf_map_affine_of_pos` expects the scaling map in affine form.
  rw [show (fun y : ℝ ↦ (a / b) * y) = fun y ↦ 0 + (a / b) * y by
    funext y
    ring]
  rw [cdf_map_affine_of_pos (a := 0) (b := a / b) (div_pos ha hb)]
  simp only [sub_zero]
  rw [cdf_fisherSnedecorMeasure_eq (mul_pos (by norm_num) ha)
    (mul_pos (by norm_num) hb)]
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx,
      ite_eq_left (div_nonpos_of_nonpos_of_nonneg hx (div_pos ha hb).le)]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [ite_eq_right hx,
      ite_eq_right (not_le.mpr (div_pos hx' (div_pos ha hb)))]
    have ha2 : 2 * a / 2 = a := by ring
    have hb2 : 2 * b / 2 = b := by ring
    have harg :
        2 * a * (x / (a / b)) / (2 * b + 2 * a * (x / (a / b))) = x / (1 + x) := by
      field_simp [ha.ne', hb.ne', (ne_of_gt (by linarith [hx'] : 0 < 1 + x))]
    rw [ha2, hb2, harg]

end TauCeti.Probability
