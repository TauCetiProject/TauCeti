/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Arcsine.Basic
public import TauCeti.Probability.Density

/-!
# The elementary arcsine density

The arcsine law has density `1 / (π * √(x * (1 - x)))` on the open unit interval,
and zero elsewhere. Identifying it with the beta density supplies the density,
`HasPDF`, and Radon–Nikodym interfaces without another normalization argument.
The assigned endpoint values are zero; the density is unbounded near both endpoints.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The real arcsine density, with value zero outside the open unit interval. -/
def arcsinePDFReal (x : ℝ) : ℝ :=
  if x ∈ Ioo 0 1 then 1 / (π * √(x * (1 - x))) else 0

/-- The extended nonnegative arcsine density. -/
def arcsinePDF (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (arcsinePDFReal x)

/-- The elementary formula for the real arcsine density, including its endpoint convention. -/
theorem arcsinePDFReal_def (x : ℝ) :
    arcsinePDFReal x = if x ∈ Ioo 0 1 then 1 / (π * √(x * (1 - x))) else 0 := (rfl)

/-- On the open unit interval the arcsine density is the reciprocal square-root formula. -/
@[simp]
theorem arcsinePDFReal_of_mem {x : ℝ} (hx : x ∈ Ioo 0 1) :
    arcsinePDFReal x = 1 / (π * √(x * (1 - x))) := by
  simp [arcsinePDFReal_def, hx]

/-- The chosen arcsine density vanishes outside the open unit interval. -/
@[simp]
theorem arcsinePDFReal_of_notMem {x : ℝ} (hx : x ∉ Ioo 0 1) : arcsinePDFReal x = 0 := by
  simp [arcsinePDFReal_def, hx]

/-- The extended arcsine density is the nonnegative embedding of the real density. -/
theorem arcsinePDF_eq_ofReal (x : ℝ) : arcsinePDF x = ENNReal.ofReal (arcsinePDFReal x) := (rfl)

/-- The elementary arcsine density agrees pointwise with the symmetric half-shape beta density. -/
theorem arcsinePDFReal_eq_betaPDFReal (x : ℝ) :
    arcsinePDFReal x = betaPDFReal (1 / 2) (1 / 2) x := by
  have hbeta : beta (1 / 2) (1 / 2) = π := by
    norm_num [beta, Gamma_one_half_eq, mul_self_sqrt pi_pos.le]
  have hhalf : (1 : ℝ) / 2 - 1 = -(1 / 2) := by norm_num
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [arcsinePDFReal_of_mem hx, betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩, hbeta,
      hhalf, rpow_neg hx.1.le, rpow_neg (sub_nonneg.mpr hx.2.le),
      ← sqrt_eq_rpow, ← sqrt_eq_rpow, sqrt_mul hx.1.le]
    ring
  · simp only [mem_Ioo] at hx
    simp [betaPDFReal, hx]

/-- The arcsine density is nonnegative everywhere. -/
theorem arcsinePDFReal_nonneg (x : ℝ) : 0 ≤ arcsinePDFReal x := by
  rw [arcsinePDFReal_def]
  split_ifs <;> positivity

/-- The density is strictly positive exactly on the open unit interval. -/
@[simp]
theorem arcsinePDFReal_pos_iff (x : ℝ) : 0 < arcsinePDFReal x ↔ x ∈ Ioo 0 1 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp only [arcsinePDFReal_of_mem hx, hx, iff_true]
    exact one_div_pos.mpr (mul_pos pi_pos (sqrt_pos.mpr (mul_pos hx.1 (sub_pos.mpr hx.2))))
  · simp [hx]

/-- Converting the extended arcsine density to a real recovers the named real density. -/
@[simp]
theorem toReal_arcsinePDF (x : ℝ) : (arcsinePDF x).toReal = arcsinePDFReal x := by
  rw [arcsinePDF_eq_ofReal, ENNReal.toReal_ofReal (arcsinePDFReal_nonneg x)]

/-- The real arcsine density is measurable. -/
@[fun_prop]
theorem measurable_arcsinePDFReal : Measurable arcsinePDFReal := by
  rw [funext arcsinePDFReal_eq_betaPDFReal]
  exact measurable_betaPDFReal _ _

/-- The extended arcsine density is measurable. -/
@[fun_prop]
theorem measurable_arcsinePDF : Measurable arcsinePDF :=
  measurable_arcsinePDFReal.ennreal_ofReal

/-- The arcsine law is Lebesgue measure weighted by its elementary density. -/
theorem arcsineMeasure_eq_withDensity : arcsineMeasure = volume.withDensity arcsinePDF := by
  rw [arcsineMeasure_eq_betaMeasure, betaMeasure]
  congr 1
  funext x
  rw [arcsinePDF_eq_ofReal, arcsinePDFReal_eq_betaPDFReal, betaPDF]

/-- An arcsine random variable has a probability density. -/
theorem hasPDF_of_hasLaw_arcsineMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X arcsineMeasure P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity measurable_arcsinePDF.aemeasurable
    (arcsineMeasure_eq_withDensity ▸ hX)

/-- The density of an arcsine random variable is the named elementary density. -/
theorem pdf_eq_arcsinePDF_of_hasLaw_arcsineMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X arcsineMeasure P) :
    pdf X P =ᵐ[volume] arcsinePDF :=
  pdf_eq_of_hasLaw_withDensity measurable_arcsinePDF.aemeasurable
    (arcsineMeasure_eq_withDensity ▸ hX)

/-- The Radon–Nikodym derivative of the arcsine law is its named elementary density. -/
theorem rnDeriv_arcsineMeasure : arcsineMeasure.rnDeriv volume =ᵐ[volume] arcsinePDF := by
  rw [arcsineMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume measurable_arcsinePDF

end TauCeti.Probability
