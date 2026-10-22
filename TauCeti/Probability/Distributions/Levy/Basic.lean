/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Lévy distribution: measure and density

The Lévy law with location `m` and scale `c > 0` is the inverse-gamma law of shape `1 / 2` and
scale `c / 2`, translated by `m`. On `(m, ∞)` it has density

`√(c / (2π)) * (x - m) ^ (-3 / 2) * exp (-c / (2 (x - m)))`.

For a nonpositive scale the inverse-gamma law is the zero measure, and so is the Lévy law.

The density is inherited from the inverse-gamma density through translation, using
`Real.Gamma_one_half_eq` to identify the normalizing constant. Positive affine maps act on the
parameters by `(m, c) ↦ (a + b m, b c)`, through the scaling identity
`inverseGammaMeasure_map_const_mul`; in particular every Lévy law is an affine image of the
standard law `levyMeasure 0 1`.

## Main declarations

* `TauCeti.Probability.levyMeasure`, `levyPDFReal` and `levyPDF` define the law and its density;
* `isProbabilityMeasure_levyMeasure` and `ae_lt_levyMeasure` give normalization and the
  almost-sure carrier `(m, ∞)`;
* `levyMeasure_eq_withDensity`, `hasPDF_of_hasLaw_levyMeasure` and `rnDeriv_levyMeasure` identify
  the density;
* `map_affine_levyMeasure` and `hasLaw_affine_levyMeasure` give positive affine transport, and
  `levyMeasure_eq_map_affine_levyMeasure_zero_one` writes every law as an image of the standard one;
* `measurable_levyMeasure` proves joint measurability in the parameters.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer (2020),
  chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m c x : ℝ}

/-! ### Definition and boundary behavior -/

/-- The Lévy law with location `m` and scale `c`: the inverse-gamma law of shape `1 / 2` and scale
`c / 2`, translated by `m`. It is the zero measure if `c ≤ 0`. -/
def levyMeasure (m c : ℝ) : Measure ℝ :=
  (inverseGammaMeasure (1 / 2) (c / 2)).map (m + ·)

/-- The defining translation of the inverse-gamma law. -/
theorem levyMeasure_def (m c : ℝ) :
    levyMeasure m c = (inverseGammaMeasure (1 / 2) (c / 2)).map (m + ·) := (rfl)

/-- At location zero the Lévy law is the inverse-gamma law of shape `1 / 2` and scale `c / 2`. -/
theorem levyMeasure_zero_left (c : ℝ) :
    levyMeasure 0 c = inverseGammaMeasure (1 / 2) (c / 2) := by
  simp [levyMeasure_def]

/-- For a nonpositive scale, the totalized Lévy law is the zero measure. -/
@[simp]
theorem levyMeasure_of_nonpos (hc : c ≤ 0) (m : ℝ) : levyMeasure m c = 0 := by
  rw [levyMeasure_def, inverseGammaMeasure_of_not_pos (fun h ↦ by linarith [h.2]),
    Measure.map_zero]

/-- A Lévy law with positive scale is a probability measure. -/
theorem isProbabilityMeasure_levyMeasure (hc : 0 < c) (m : ℝ) :
    IsProbabilityMeasure (levyMeasure m c) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure one_half_pos (half_pos hc)
  rw [levyMeasure_def]
  infer_instance

/-- A Lévy law gives no mass to the half-line `(-∞, m]` at and below its location. -/
@[simp]
theorem levyMeasure_Iic_self (m c : ℝ) : levyMeasure m c (Iic m) = 0 := by
  have hpre : (m + ·) ⁻¹' Iic m = Iic (0 : ℝ) := by
    ext y
    simp
  rw [levyMeasure_def, Measure.map_apply (measurable_const_add m) measurableSet_Iic, hpre,
    inverseGammaMeasure_Iic_zero]

/-- A Lévy variable lies strictly above its location almost surely. -/
theorem ae_lt_levyMeasure (m c : ℝ) : ∀ᵐ x ∂levyMeasure m c, m < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using levyMeasure_Iic_self m c

/-! ### Density -/

/-- The real-valued Lévy density. It vanishes unless the scale is positive and the sample point
lies above the location. -/
def levyPDFReal (m c x : ℝ) : ℝ :=
  if 0 < c ∧ m < x then
    √(c / (2 * π)) * (x - m) ^ (-(3 / 2 : ℝ)) * exp (-c / (2 * (x - m)))
  else 0

/-- The Lévy density, valued in `ℝ≥0∞`. -/
def levyPDF (m c x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (levyPDFReal m c x)

/-- The `ℝ≥0∞`-valued Lévy density is the coercion of the real-valued one. -/
theorem levyPDF_eq_ofReal (m c x : ℝ) :
    levyPDF m c x = ENNReal.ofReal (levyPDFReal m c x) := (rfl)

/-- The real Lévy density has its usual formula above the location at positive scale. -/
@[simp]
theorem levyPDFReal_of_lt (hc : 0 < c) (hx : m < x) :
    levyPDFReal m c x =
      √(c / (2 * π)) * (x - m) ^ (-(3 / 2 : ℝ)) * exp (-c / (2 * (x - m))) := by
  simp [levyPDFReal, hc, hx]

/-- The Lévy density vanishes at and below the location. -/
@[simp]
theorem levyPDFReal_of_le (hx : x ≤ m) (c : ℝ) : levyPDFReal m c x = 0 := by
  simp [levyPDFReal, not_lt.mpr hx]

/-- The Lévy density vanishes for a nonpositive scale. -/
@[simp]
theorem levyPDFReal_of_nonpos (hc : c ≤ 0) (m x : ℝ) : levyPDFReal m c x = 0 := by
  simp [levyPDFReal, not_lt.mpr hc]

/-- The Lévy density is the inverse-gamma density of shape `1 / 2` and scale `c / 2` at the
translated point `x - m`. -/
theorem levyPDFReal_eq_inverseGammaPDFReal (m c x : ℝ) :
    levyPDFReal m c x = inverseGammaPDFReal (1 / 2) (c / 2) (x - m) := by
  by_cases hc : 0 < c
  · rcases le_or_gt x m with hx | hx
    · rw [levyPDFReal_of_le hx, inverseGammaPDFReal_of_nonpos (sub_nonpos.mpr hx)]
    · rw [levyPDFReal_of_lt hc hx,
        inverseGammaPDFReal_of_pos one_half_pos (half_pos hc) (sub_pos.mpr hx),
        Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_div' _ pi_pos.le,
        div_div]
      congr 2
      · norm_num
      · field_simp
  · rw [levyPDFReal_of_nonpos (not_lt.mp hc),
      inverseGammaPDFReal_of_not_pos (fun h ↦ hc (by linarith [h.2]))]

/-- The real-valued Lévy density is nonnegative. -/
theorem levyPDFReal_nonneg (m c x : ℝ) : 0 ≤ levyPDFReal m c x := by
  rw [levyPDFReal_eq_inverseGammaPDFReal]
  exact inverseGammaPDFReal_nonneg _ _ _

/-- Converting the Lévy density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_levyPDF (m c x : ℝ) : (levyPDF m c x).toReal = levyPDFReal m c x := by
  rw [levyPDF_eq_ofReal, ENNReal.toReal_ofReal (levyPDFReal_nonneg m c x)]

/-- The Lévy density has its usual formula above the location at positive scale. -/
@[simp]
theorem levyPDF_of_lt (hc : 0 < c) (hx : m < x) :
    levyPDF m c x =
      ENNReal.ofReal (√(c / (2 * π)) * (x - m) ^ (-(3 / 2 : ℝ)) * exp (-c / (2 * (x - m)))) := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_lt hc hx]

/-- The `ℝ≥0∞`-valued Lévy density vanishes at and below the location. -/
@[simp]
theorem levyPDF_of_le (hx : x ≤ m) (c : ℝ) : levyPDF m c x = 0 := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_le hx, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued Lévy density vanishes for a nonpositive scale. -/
@[simp]
theorem levyPDF_of_nonpos (hc : c ≤ 0) (m x : ℝ) : levyPDF m c x = 0 := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_nonpos hc, ENNReal.ofReal_zero]

/-- The real Lévy density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_levyPDFReal (m c : ℝ) : Measurable (levyPDFReal m c) := by
  simp_rw [funext (levyPDFReal_eq_inverseGammaPDFReal m c)]
  exact (measurable_inverseGammaPDFReal _ _).comp (measurable_sub_const m)

/-- The `ℝ≥0∞`-valued Lévy density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_levyPDF (m c : ℝ) : Measurable (levyPDF m c) :=
  (measurable_levyPDFReal m c).ennreal_ofReal

/-- **The density of a Lévy law**, including the zero density at a nonpositive scale. -/
theorem levyMeasure_eq_withDensity (m c : ℝ) :
    levyMeasure m c = volume.withDensity (levyPDF m c) := by
  have hadd : (m + ·) = (· + m) := funext fun x ↦ add_comm m x
  rw [levyMeasure_def, hadd, inverseGammaMeasure_eq_withDensity, Measure.map_add_right_withDensity]
  congr 1
  funext x
  rw [levyPDF_eq_ofReal, levyPDFReal_eq_inverseGammaPDFReal, inverseGammaPDF_eq_ofReal]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a Lévy law has a density. -/
theorem hasPDF_of_hasLaw_levyMeasure (hX : HasLaw X (levyMeasure m c) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_levyPDF m c).aemeasurable
    (by rwa [levyMeasure_eq_withDensity m c] at hX)

/-- The density of a random variable with a Lévy law is `levyPDF`. -/
theorem pdf_eq_levyPDF_of_hasLaw_levyMeasure (hX : HasLaw X (levyMeasure m c) P) :
    pdf X P volume =ᵐ[volume] levyPDF m c :=
  pdf_eq_of_hasLaw_withDensity (measurable_levyPDF m c).aemeasurable
    (by rwa [levyMeasure_eq_withDensity m c] at hX)

/-- The Radon–Nikodym derivative of a Lévy law against Lebesgue measure. -/
theorem rnDeriv_levyMeasure (m c : ℝ) :
    (levyMeasure m c).rnDeriv volume =ᵐ[volume] levyPDF m c := by
  rw [levyMeasure_eq_withDensity m c]
  exact Measure.rnDeriv_withDensity volume (measurable_levyPDF m c)

/-! ### Affine transport and parameter measurability -/

/-- **Positive affine transport.** For `b > 0`, the law of `a + b X` for a Lévy variable `X` with
location `m` and scale `c` is the Lévy law with location `a + b * m` and scale `b * c`. The
identity also respects the nonpositive-scale zero-measure branch. -/
theorem map_affine_levyMeasure {b : ℝ} (hb : 0 < b) (a m c : ℝ) :
    (levyMeasure m c).map (fun x ↦ a + b * x) = levyMeasure (a + b * m) (b * c) := by
  have hfun : (fun x : ℝ ↦ a + b * x) ∘ (m + ·) = (a + b * m + ·) ∘ (b * ·) := by
    funext x
    simp only [Function.comp_apply]
    ring
  rw [levyMeasure_def, levyMeasure_def, Measure.map_map (by fun_prop) (by fun_prop), hfun,
    ← Measure.map_map (by fun_prop) (by fun_prop), inverseGammaMeasure_map_const_mul hb,
    mul_div_assoc]

/-- The random-variable form of positive affine transport of the Lévy law. -/
theorem hasLaw_affine_levyMeasure {b : ℝ} (hb : 0 < b) (a : ℝ)
    (hX : HasLaw X (levyMeasure m c) P) :
    HasLaw (fun ω ↦ a + b * X ω) (levyMeasure (a + b * m) (b * c)) P := by
  rw [← map_affine_levyMeasure hb]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ ↦ a + b * x).aemeasurable).comp hX

/-- Every Lévy law with positive scale is an affine image of the standard Lévy law. -/
theorem levyMeasure_eq_map_affine_levyMeasure_zero_one (hc : 0 < c) (m : ℝ) :
    levyMeasure m c = (levyMeasure 0 1).map (fun x ↦ m + c * x) := by
  rw [map_affine_levyMeasure hc, mul_zero, add_zero, mul_one]

/-- The Lévy family is jointly measurable in its location and scale, including the
nonpositive-scale zero-measure branch. -/
@[fun_prop]
theorem measurable_levyMeasure : Measurable fun p : ℝ × ℝ ↦ levyMeasure p.1 p.2 := by
  have heq : (fun p : ℝ × ℝ ↦ levyMeasure p.1 p.2) = fun p ↦
      if 0 < p.2 then (levyMeasure 0 1).map (fun x ↦ p.1 + p.2 * x) else 0 := by
    funext p
    split_ifs with hp
    · exact levyMeasure_eq_map_affine_levyMeasure_zero_one hp p.1
    · exact levyMeasure_of_nonpos (not_lt.mp hp) p.1
  rw [heq]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  let _ := isProbabilityMeasure_levyMeasure one_pos 0
  exact TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
    (ν := levyMeasure 0 1) (f := fun p : ℝ × ℝ ↦ fun x ↦ p.1 + p.2 * x) (by fun_prop)

end Probability

end TauCeti
