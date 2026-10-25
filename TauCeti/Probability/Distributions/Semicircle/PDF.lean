/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Basic
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Density of the semicircle law

The unit-radius semicircle law has the continuous density `2 / π * √(1 - x²)`.
The real square root makes this expression zero outside the open interval `(-1, 1)`,
in particular at the endpoints `±1`.
The affine Beta realization gives the density-measure equality and the random-variable
and Radon–Nikodym interfaces.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

/-- The real density of the unit-radius semicircle law, zero outside `(-1, 1)`. -/
def semicirclePDFReal (x : ℝ) : ℝ := 2 / π * √(1 - x ^ 2)

/-- The extended nonnegative density of the unit-radius semicircle law. -/
def semicirclePDF (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (semicirclePDFReal x)

/-- The semicircle density is the scaled height of the unit semicircle. -/
theorem semicirclePDFReal_apply (x : ℝ) :
    semicirclePDFReal x = 2 / π * √(1 - x ^ 2) := (rfl)

/-- The extended density is obtained from the real density by `ENNReal.ofReal`. -/
@[simp]
theorem semicirclePDF_apply (x : ℝ) :
    semicirclePDF x = ENNReal.ofReal (semicirclePDFReal x) := (rfl)

/-- The semicircle density is nonnegative. -/
theorem semicirclePDFReal_nonneg (x : ℝ) : 0 ≤ semicirclePDFReal x := by
  exact mul_nonneg (by positivity) (sqrt_nonneg _)

/-- The density is positive exactly in the interior of the support. -/
@[simp]
theorem semicirclePDFReal_pos_iff {x : ℝ} :
    0 < semicirclePDFReal x ↔ x ∈ Ioo (-1 : ℝ) 1 := by
  rw [semicirclePDFReal_apply, mul_pos_iff_of_pos_left (by positivity), sqrt_pos]
  constructor
  · intro hx
    constructor <;> nlinarith
  · rintro ⟨hl, hr⟩
    nlinarith [mul_pos (by linarith : 0 < x + 1) (by linarith : 0 < 1 - x)]

/-- The real density is continuous, including at the support endpoints. -/
@[fun_prop]
theorem continuous_semicirclePDFReal : Continuous semicirclePDFReal := by
  unfold semicirclePDFReal
  fun_prop

/-- The extended density is measurable. -/
@[fun_prop]
theorem measurable_semicirclePDF : Measurable semicirclePDF :=
  continuous_semicirclePDFReal.measurable.ennreal_ofReal

private lemma half_betaPDFReal (x : ℝ) :
    (1 / 2 : ℝ) * betaPDFReal (3 / 2) (3 / 2) ((x + 1) / 2) =
      semicirclePDFReal x := by
  rw [betaPDFReal, semicirclePDFReal_apply]
  split_ifs with hx
  · rw [beta_three_halves_three_halves]
    norm_num only [show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num, ← sqrt_eq_rpow]
    rw [mul_assoc, ← sqrt_mul (by linarith : 0 ≤ (x + 1) / 2),
      show (x + 1) / 2 * (1 - (x + 1) / 2) = (1 - x ^ 2) / 4 by ring,
      sqrt_div (by nlinarith [hx.1, hx.2])]
    rw [show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    ring
  · rw [sqrt_eq_zero_of_nonpos (by
      push Not at hx
      by_cases hl : 0 < (x + 1) / 2
      · have := hx hl; nlinarith
      · push Not at hl; nlinarith)]
    simp

/-- The semicircle law is Lebesgue measure weighted by its named density. -/
theorem semicircleMeasure_eq_withDensity :
    semicircleMeasure = volume.withDensity semicirclePDF := by
  rw [semicircleMeasure_eq_map_betaMeasure, betaMeasure,
    map_affine_withDensity_volume _ (by norm_num)]
  congr 1
  ext x
  rw [affineDensity_apply, semicirclePDF_apply, ← half_betaPDFReal]
  simp only [betaPDF, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show x - -1 = x + 1 by ring]
  norm_num

/-- The semicircle law has no atoms. -/
instance nullSingletonClass_semicircleMeasure : NullSingletonClass semicircleMeasure := by
  rw [semicircleMeasure_eq_withDensity]
  infer_instance

/-- A variable with semicircle law has a density. -/
theorem hasPDF_of_hasLaw_semicircleMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X semicircleMeasure P) : HasPDF X P := by
  rw [semicircleMeasure_eq_withDensity] at hX
  exact hasPDF_of_hasLaw_withDensity measurable_semicirclePDF.aemeasurable hX

/-- The density of a variable with semicircle law agrees almost everywhere with its named pdf. -/
theorem pdf_eq_semicirclePDF_of_hasLaw_semicircleMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X semicircleMeasure P) :
    pdf X P =ᵐ[volume] semicirclePDF := by
  rw [semicircleMeasure_eq_withDensity] at hX
  exact pdf_eq_of_hasLaw_withDensity measurable_semicirclePDF.aemeasurable hX

/-- The Radon–Nikodym derivative of the semicircle law is its named pdf. -/
theorem rnDeriv_semicircleMeasure :
    semicircleMeasure.rnDeriv volume =ᵐ[volume] semicirclePDF := by
  rw [semicircleMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume measurable_semicirclePDF

end TauCeti.Probability
