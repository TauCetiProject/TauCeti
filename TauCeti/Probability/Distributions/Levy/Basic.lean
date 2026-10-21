/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf
public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.InverseGamma.Cdf

import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Lévy distribution: measure, density, support, and cdf

The Lévy law with location `m` and scale `c > 0` is the inverse-gamma law of shape `1 / 2` and
scale `c / 2`, translated by `m`. This file defines it, derives its density

`√(c / (2π)) * (x - m) ^ (-3 / 2) * exp (-c / (2 (x - m)))`

on `(m, ∞)`, identifies its topological support `[m, ∞)`, proves parameter measurability, and
computes its cdf `erfc √(c / (2 (x - m)))`. It also shows that the family is closed under affine
maps of positive slope, with location `a + b m` and scale `b c`.

For nonpositive scale the inverse-gamma law, and hence the Lévy law, is the zero measure.

## Main declarations

* `TauCeti.Probability.levyMeasure`, `levyPDFReal`, and `levyPDF` define the law and its density;
* `levyMeasure_eq_withDensity`, `hasPDF_of_hasLaw_levyMeasure`, and `rnDeriv_levyMeasure`
  identify the density, and `support_levyMeasure` the support;
* `measurable_levyMeasure` gives parameter measurability;
* `cdf_levyMeasure_eq` is the closed-form cdf;
* `levyMeasure_map_affine` is the affine transport identity.

## References

* J. P. Nolan, *Univariate Stable Distributions*, Springer (2020), chapter 1.
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
`c / 2` translated by `m`. It is the zero measure when `c ≤ 0`. -/
def levyMeasure (m c : ℝ) : Measure ℝ :=
  (inverseGammaMeasure (1 / 2) (c / 2)).map (m + ·)

/-- The defining translation of the inverse-gamma law. -/
theorem levyMeasure_def (m c : ℝ) :
    levyMeasure m c = (inverseGammaMeasure (1 / 2) (c / 2)).map (m + ·) := (rfl)

/-- For nonpositive scale the Lévy law is the zero measure. -/
@[simp]
theorem levyMeasure_of_nonpos (hc : c ≤ 0) (m : ℝ) : levyMeasure m c = 0 := by
  rw [levyMeasure_def, inverseGammaMeasure_of_not_pos (by grind), Measure.map_zero]

/-- A Lévy law with positive scale is a probability measure. -/
theorem isProbabilityMeasure_levyMeasure (hc : 0 < c) (m : ℝ) :
    IsProbabilityMeasure (levyMeasure m c) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure one_half_pos (half_pos hc)
  rw [levyMeasure_def]
  infer_instance

/-- The Lévy law assigns no mass to the half-line at or below its location. -/
@[simp]
theorem levyMeasure_Iic (m c : ℝ) : levyMeasure m c (Iic m) = 0 := by
  have hpre : (m + ·) ⁻¹' Iic m = Iic (0 : ℝ) := by
    ext y
    simp
  rw [levyMeasure_def, Measure.map_apply (by fun_prop) measurableSet_Iic, hpre,
    inverseGammaMeasure_Iic_zero]

/-- A Lévy law is concentrated strictly above its location. -/
theorem ae_lt_levyMeasure (m c : ℝ) : ∀ᵐ x ∂levyMeasure m c, m < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using levyMeasure_Iic m c

/-! ### Density -/

/-- The real-valued Lévy density. It vanishes unless the scale is positive and the sample point
lies above the location. -/
def levyPDFReal (m c x : ℝ) : ℝ :=
  if 0 < c ∧ m < x then
    √(c / (2 * π)) * (x - m) ^ (-(3 / 2) : ℝ) * exp (-c / (2 * (x - m)))
  else 0

/-- The Lévy density, valued in `ℝ≥0∞`. -/
def levyPDF (m c x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (levyPDFReal m c x)

/-- The `ℝ≥0∞`-valued Lévy density is the coercion of the real-valued one. -/
theorem levyPDF_eq_ofReal (m c x : ℝ) : levyPDF m c x = ENNReal.ofReal (levyPDFReal m c x) :=
  (rfl)

/-- The real Lévy density above the location at positive scale. -/
@[simp]
theorem levyPDFReal_of_lt (hc : 0 < c) (hx : m < x) :
    levyPDFReal m c x =
      √(c / (2 * π)) * (x - m) ^ (-(3 / 2) : ℝ) * exp (-c / (2 * (x - m))) := by
  simp [levyPDFReal, hc, hx]

/-- The real Lévy density vanishes at or below the location. -/
@[simp]
theorem levyPDFReal_of_le (hx : x ≤ m) (c : ℝ) : levyPDFReal m c x = 0 := by
  simp [levyPDFReal, not_lt.mpr hx]

/-- The real Lévy density vanishes at nonpositive scale. -/
@[simp]
theorem levyPDFReal_of_nonpos (hc : c ≤ 0) (m x : ℝ) : levyPDFReal m c x = 0 := by
  simp [levyPDFReal, not_lt.mpr hc]

/-- The Lévy density above the location at positive scale. -/
@[simp]
theorem levyPDF_of_lt (hc : 0 < c) (hx : m < x) :
    levyPDF m c x = ENNReal.ofReal
      (√(c / (2 * π)) * (x - m) ^ (-(3 / 2) : ℝ) * exp (-c / (2 * (x - m)))) := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_lt hc hx]

/-- The Lévy density vanishes at or below the location. -/
@[simp]
theorem levyPDF_of_le (hx : x ≤ m) (c : ℝ) : levyPDF m c x = 0 := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_le hx, ENNReal.ofReal_zero]

/-- The Lévy density vanishes at nonpositive scale. -/
@[simp]
theorem levyPDF_of_nonpos (hc : c ≤ 0) (m x : ℝ) : levyPDF m c x = 0 := by
  rw [levyPDF_eq_ofReal, levyPDFReal_of_nonpos hc, ENNReal.ofReal_zero]

/-- The real Lévy density is the inverse-gamma density of shape `1 / 2` and scale `c / 2` at the
translated point `x - m`, for every parameter value. -/
theorem levyPDFReal_eq_inverseGammaPDFReal (m c x : ℝ) :
    levyPDFReal m c x = inverseGammaPDFReal (1 / 2) (c / 2) (x - m) := by
  by_cases hc : 0 < c
  · by_cases hx : m < x
    · have hxm : 0 < x - m := sub_pos.mpr hx
      rw [levyPDFReal_of_lt hc hx,
        inverseGammaPDFReal_of_pos one_half_pos (half_pos hc) hxm, Real.Gamma_one_half_eq,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_div' _ pi_pos.le, div_div]
      congr 2
      · norm_num
      · field_simp
    · rw [levyPDFReal_of_le (not_lt.mp hx), inverseGammaPDFReal_of_nonpos (by linarith)]
  · rw [levyPDFReal_of_nonpos (not_lt.mp hc),
      inverseGammaPDFReal_of_not_pos (fun h ↦ hc (by linarith [h.2]))]

/-- The Lévy density is the inverse-gamma density of shape `1 / 2` and scale `c / 2` at the
translated point `x - m`. -/
theorem levyPDF_eq_inverseGammaPDF (m c x : ℝ) :
    levyPDF m c x = inverseGammaPDF (1 / 2) (c / 2) (x - m) := by
  rw [levyPDF_eq_ofReal, levyPDFReal_eq_inverseGammaPDFReal, inverseGammaPDF_eq_ofReal]

/-- The real Lévy density is nonnegative. -/
theorem levyPDFReal_nonneg (m c x : ℝ) : 0 ≤ levyPDFReal m c x := by
  rw [levyPDFReal_eq_inverseGammaPDFReal]
  exact inverseGammaPDFReal_nonneg _ _ _

/-- The real Lévy density is positive exactly above the location, at positive scale. -/
theorem levyPDFReal_pos_iff (hc : 0 < c) : 0 < levyPDFReal m c x ↔ m < x := by
  refine ⟨fun h ↦ not_le.mp fun hx ↦ by simp [levyPDFReal_of_le hx] at h, fun hx ↦ ?_⟩
  rw [levyPDFReal_of_lt hc hx]
  have : 0 < x - m := sub_pos.mpr hx
  positivity

/-- Converting the Lévy density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_levyPDF (m c x : ℝ) : (levyPDF m c x).toReal = levyPDFReal m c x := by
  rw [levyPDF_eq_ofReal, ENNReal.toReal_ofReal (levyPDFReal_nonneg m c x)]

/-- The real Lévy density is measurable jointly in its location, its scale and the point. -/
@[fun_prop]
theorem measurable_uncurry_levyPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ levyPDFReal q.1.1 q.1.2 q.2 := by
  simp only [levyPDFReal]
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_fst.snd).inter
    (measurableSet_lt measurable_fst.fst measurable_snd)) (by fun_prop) measurable_const

/-- The `ℝ≥0∞`-valued Lévy density is measurable jointly in its parameters and the point. -/
@[fun_prop]
theorem measurable_uncurry_levyPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ levyPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_levyPDFReal.ennreal_ofReal

/-- The real Lévy density is measurable. -/
@[fun_prop]
theorem measurable_levyPDFReal (m c : ℝ) : Measurable (levyPDFReal m c) :=
  measurable_uncurry_levyPDFReal.comp (measurable_prodMk_left (x := (m, c)))

/-- The `ℝ≥0∞`-valued Lévy density is measurable. -/
@[fun_prop]
theorem measurable_levyPDF (m c : ℝ) : Measurable (levyPDF m c) :=
  (measurable_levyPDFReal m c).ennreal_ofReal

/-- **The density of a Lévy law**, including the zero density at nonpositive scale. -/
theorem levyMeasure_eq_withDensity (m c : ℝ) :
    levyMeasure m c = volume.withDensity (levyPDF m c) := by
  have htrans : (m + · : ℝ → ℝ) = fun x ↦ m + 1 * x := by
    ext x
    rw [one_mul]
  rw [levyMeasure_def, inverseGammaMeasure_eq_withDensity, htrans,
    map_affine_withDensity_volume _ one_ne_zero]
  congr 1
  ext y
  rw [affineDensity_apply, abs_one, inv_one, ENNReal.ofReal_one, one_mul, div_one,
    levyPDF_eq_inverseGammaPDF]

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

/-! ### Support -/

/-- At positive scale, the function support of the Lévy density is the open half-line above the
location. -/
@[simp]
theorem support_levyPDF (hc : 0 < c) (m : ℝ) : Function.support (levyPDF m c) = Ioi m := by
  ext x
  rw [Function.mem_support, levyPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff, mem_Ioi]
  exact levyPDFReal_pos_iff hc

/-- At positive scale, the topological support of a Lévy law is the closed half-line `[m, ∞)`. -/
@[simp]
theorem support_levyMeasure (hc : 0 < c) (m : ℝ) : (levyMeasure m c).support = Ici m := by
  rw [levyMeasure_eq_withDensity, Measure.support_withDensity_eq_closure (measurable_levyPDF m c)
    isOpen_Ioi (support_levyPDF hc m), closure_Ioi]

/-! ### Parameter measurability -/

/-- The Lévy family is jointly measurable in its location and scale. -/
@[fun_prop]
theorem measurable_levyMeasure : Measurable fun p : ℝ × ℝ ↦ levyMeasure p.1 p.2 := by
  simp only [levyMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_levyPDF

/-! ### Cumulative distribution function -/

/-- **The cdf of a Lévy law** is `erfc √(c / (2 (x - m)))` above the location and zero at or
below it. -/
@[simp]
theorem cdf_levyMeasure_eq (hc : 0 < c) (m x : ℝ) :
    cdf (levyMeasure m c) x = if x ≤ m then 0 else Real.erfc √(c / (2 * (x - m))) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure one_half_pos (half_pos hc)
  have htrans : (m + · : ℝ → ℝ) = fun y ↦ m + 1 * y := by
    ext y
    rw [one_mul]
  rw [levyMeasure_def, htrans, cdf_map_affine_of_pos one_pos, div_one,
    cdf_inverseGammaMeasure_eq one_half_pos (half_pos hc)]
  by_cases hx : x ≤ m
  · simp [hx]
  · have hxm : 0 < x - m := sub_pos.mpr (not_le.mp hx)
    rw [ite_eq_right (not_le.mpr hxm), ite_eq_right hx, Real.erfc_def,
      Real.erf_eq_regularizedGamma_half_sq (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
      div_div]

/-! ### Affine transport -/

/-- **Affine transport of a Lévy law.** Under `x ↦ a + b x` with `b > 0`, the Lévy law with location
`m` and scale `c` becomes the Lévy law with location `a + b m` and scale `b c`. -/
@[simp]
theorem levyMeasure_map_affine {b : ℝ} (hb : 0 < b) (a m c : ℝ) :
    (levyMeasure m c).map (fun x ↦ a + b * x) = levyMeasure (a + b * m) (b * c) := by
  have hcomp : (fun x : ℝ ↦ a + b * x) ∘ (m + ·) = (a + b * m + ·) ∘ (b * ·) := by
    ext x
    simp only [Function.comp_apply]
    ring
  rw [levyMeasure_def, levyMeasure_def, Measure.map_map (by fun_prop) (by fun_prop), hcomp,
    ← Measure.map_map (by fun_prop) (by fun_prop), inverseGammaMeasure_map_const_mul hb,
    mul_div_assoc]

end Probability

end TauCeti
