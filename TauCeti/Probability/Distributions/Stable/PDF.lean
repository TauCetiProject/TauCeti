/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.CharFun.Inversion
public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Stable.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import TauCeti.MeasureTheory.Integral.Gamma

/-!
# The density of a scalar stable law

A stable law `stableMeasure α β s m` with positive scale `s` has characteristic function `φ` of
modulus `|φ(t)| = exp (-|s t| ^ α)`, which is integrable on the real line. Fourier inversion
(`MeasureTheory.Measure.eq_withDensity_charFunDensity`) therefore gives the law a bounded
continuous density

`f(x) = (2π)⁻¹ * Re ∫ t, exp (-i t x) * φ(t) dt`,

defined here as `stablePDFReal α β s m`. It is nonnegative and continuous for all parameters and,
for valid shapes and positive scale, bounded by `Γ(1/α) / (π α s)`, the value of `(2π)⁻¹ ∫ |φ|`.

For invalid shapes the law is zero and so is its density. At scale zero the law of a valid shape
is a Dirac mass, which has no density; its characteristic function is not integrable and
`stablePDFReal` vanishes.

## Main definitions

* `TauCeti.Probability.stablePDFReal`: the real density of a stable law.
* `TauCeti.Probability.stablePDF`: its `ℝ≥0∞`-valued companion.

## Main results

* `TauCeti.Probability.stablePDFReal_eq`: the density written through the stable characteristic
  exponent.
* `TauCeti.Probability.stablePDFReal_of_invalid` and `TauCeti.Probability.stablePDFReal_zero_scale`:
  the density vanishes for invalid shapes and at scale zero.
* `TauCeti.Probability.integrable_charFun_stableMeasure`: positive-scale stable characteristic
  functions are integrable.
* `TauCeti.Probability.stableMeasure_eq_withDensity`: for positive scale the law is
  `volume.withDensity (stablePDF α β s m)`.
* `TauCeti.Probability.stablePDFReal_nonneg`, `TauCeti.Probability.continuous_stablePDFReal` and
  `TauCeti.Probability.stablePDFReal_le`: nonnegativity, continuity and the uniform bound.
* `TauCeti.Probability.hasPDF_of_hasLaw_stableMeasure`,
  `TauCeti.Probability.pdf_eq_stablePDF_of_hasLaw_stableMeasure` and
  `TauCeti.Probability.rnDeriv_stableMeasure`: the density interfaces.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), Section XV.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal Real

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0}

/-! ### The characteristic function -/

/-- The characteristic function of a stable law of valid shape has modulus
`exp (-|s t| ^ α)`. -/
theorem norm_charFun_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (s : ℝ≥0) (m t : ℝ) :
    ‖charFun (stableMeasure α β s m) t‖ = Real.exp (-|s * t| ^ α) := by
  rw [charFun_stableMeasure hα hβ, Complex.norm_exp, add_re,
    stableCharacteristicExponent_re hα.1.ne']
  simp

/-- A stable law of positive scale has an integrable characteristic function. For invalid
shapes the law and its characteristic function are zero. -/
theorem integrable_charFun_stableMeasure (α β : ℝ) (hs : 0 < s) (m : ℝ) :
    Integrable (charFun (stableMeasure α β s m)) := by
  by_cases h : α ∈ Ioc 0 2 ∧ |β| ≤ 1
  · have hint : Integrable fun t : ℝ ↦ Real.exp (-|(s : ℝ) * t| ^ α) := by
      have h0 := (integrable_abs_rpow_mul_exp_neg_abs_rpow_iff h.1.1 (q := 0)).2 (by norm_num)
      simp only [Real.rpow_zero, one_mul] at h0
      exact h0.comp_mul_left' (NNReal.coe_pos.2 hs).ne'
    exact hint.mono' continuous_charFun.aestronglyMeasurable
      (ae_of_all _ fun t ↦ (norm_charFun_stableMeasure h.1 h.2 s m t).le)
  · rw [stableMeasure_of_invalid (by
      simpa only [mem_Ioc, not_and_or, not_lt, not_le, or_assoc] using h)]
    rw [show charFun (0 : Measure ℝ) = 0 from funext fun _ ↦ charFun_zero_measure]
    exact integrable_zero ℝ ℂ volume

/-! ### The density -/

/-- The density of the stable law `stableMeasure α β s m`: the Fourier inversion
`x ↦ (2π)⁻¹ * Re ∫ t, exp (-i t x) * φ(t) dt` of its characteristic function `φ`. It is a density
of the law for positive scale (`stableMeasure_eq_withDensity`) and vanishes for invalid shapes
and at scale zero. -/
def stablePDFReal (α β : ℝ) (s : ℝ≥0) (m x : ℝ) : ℝ :=
  (stableMeasure α β s m).charFunDensity x

/-- The `ℝ≥0∞`-valued density of the stable law. -/
def stablePDF (α β : ℝ) (s : ℝ≥0) (m x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (stablePDFReal α β s m x)

theorem stablePDFReal_def (α β : ℝ) (s : ℝ≥0) (m x : ℝ) :
    stablePDFReal α β s m x = (stableMeasure α β s m).charFunDensity x := by
  rw [stablePDFReal]

theorem stablePDF_eq_ofReal (α β : ℝ) (s : ℝ≥0) (m x : ℝ) :
    stablePDF α β s m x = ENNReal.ofReal (stablePDFReal α β s m x) := by
  rw [stablePDF]

/-- For valid shapes, the stable density is the Fourier inversion of
`t ↦ exp (i m t + Ψ_{α,β}(s t))`. -/
theorem stablePDFReal_eq (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (s : ℝ≥0) (m x : ℝ) :
    stablePDFReal α β s m x = (2 * π)⁻¹ * (∫ t : ℝ, cexp (-(t * x * I)) *
      cexp ((m * t : ℝ) * I + stableCharacteristicExponent α β (s * t))).re := by
  simp_rw [stablePDFReal_def, Measure.charFunDensity_def, charFun_stableMeasure hα hβ]

/-- For invalid shapes the stable density vanishes. -/
@[simp]
theorem stablePDFReal_of_invalid (h : α ≤ 0 ∨ 2 < α ∨ 1 < |β|) (s : ℝ≥0) (m x : ℝ) :
    stablePDFReal α β s m x = 0 := by
  simp [stablePDFReal_def, Measure.charFunDensity_def, stableMeasure_of_invalid h,
    charFun_zero_measure]

/-- At scale zero a stable law of valid shape is a Dirac mass, whose characteristic function has
modulus one and is not integrable; the stable density vanishes. -/
@[simp]
theorem stablePDFReal_zero_scale (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (m x : ℝ) :
    stablePDFReal α β 0 m x = 0 := by
  refine Measure.charFunDensity_of_not_integrable (fun h ↦ ?_) x
  have h1 : Integrable (fun _ : ℝ ↦ (1 : ℝ)) := h.norm.congr (ae_of_all _ fun t ↦ by
    simp [norm_charFun_stableMeasure hα hβ, Real.zero_rpow hα.1.ne'])
  simp only [integrable_const_iff, one_ne_zero, false_or] at h1
  simpa [Real.volume_univ] using measure_lt_top (volume : Measure ℝ) univ

/-- The stable density is nonnegative. -/
theorem stablePDFReal_nonneg (α β : ℝ) (s : ℝ≥0) (m x : ℝ) : 0 ≤ stablePDFReal α β s m x :=
  Measure.charFunDensity_nonneg x

theorem toReal_stablePDF (α β : ℝ) (s : ℝ≥0) (m x : ℝ) :
    (stablePDF α β s m x).toReal = stablePDFReal α β s m x :=
  ENNReal.toReal_ofReal (stablePDFReal_nonneg α β s m x)

/-- The stable density is continuous for all parameters. -/
@[fun_prop]
theorem continuous_stablePDFReal (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    Continuous (stablePDFReal α β s m) :=
  Measure.continuous_charFunDensity

@[fun_prop]
theorem measurable_stablePDFReal (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    Measurable (stablePDFReal α β s m) :=
  (continuous_stablePDFReal α β s m).measurable

@[fun_prop]
theorem measurable_stablePDF (α β : ℝ) (s : ℝ≥0) (m : ℝ) : Measurable (stablePDF α β s m) :=
  (measurable_stablePDFReal α β s m).ennreal_ofReal

/-- **The stable density is bounded.** For valid shapes and positive scale it is at most
`Γ(1/α) / (π α s)`, which is `(2π)⁻¹ ∫ |φ|`. -/
theorem stablePDFReal_le (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s) (m x : ℝ) :
    stablePDFReal α β s m x ≤ Real.Gamma α⁻¹ / (π * α * s) := by
  have h := integral_abs_rpow_mul_exp_neg_abs_rpow hα.1 (q := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul, zero_add, one_div] at h
  refine (Measure.charFunDensity_le _ x).trans_eq ?_
  simp_rw [norm_charFun_stableMeasure hα hβ]
  rw [Measure.integral_comp_mul_left (fun t : ℝ ↦ Real.exp (-|t| ^ α)), h, abs_inv,
    abs_of_pos (NNReal.coe_pos.2 hs), smul_eq_mul]
  field_simp

/-! ### The law as a measure with density -/

/-- **Stable laws of positive scale have a density.** The law is Lebesgue measure weighted by
`stablePDF`. This holds for invalid shapes too, where both sides vanish. -/
theorem stableMeasure_eq_withDensity (α β : ℝ) (hs : 0 < s) (m : ℝ) :
    stableMeasure α β s m = volume.withDensity (stablePDF α β s m) := by
  simp_rw [funext (stablePDF_eq_ofReal α β s m), stablePDFReal_def]
  exact Measure.eq_withDensity_charFunDensity (integrable_charFun_stableMeasure α β hs m)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ}

/-- A random variable with a positive-scale stable law has a density. -/
theorem hasPDF_of_hasLaw_stableMeasure (hs : 0 < s) (hX : HasLaw X (stableMeasure α β s m) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_stablePDF α β s m).aemeasurable
    (by rwa [stableMeasure_eq_withDensity α β hs] at hX)

/-- The density of a random variable with a positive-scale stable law is `stablePDF`. -/
theorem pdf_eq_stablePDF_of_hasLaw_stableMeasure (hs : 0 < s)
    (hX : HasLaw X (stableMeasure α β s m) P) :
    pdf X P volume =ᵐ[volume] stablePDF α β s m :=
  pdf_eq_of_hasLaw_withDensity (measurable_stablePDF α β s m).aemeasurable
    (by rwa [stableMeasure_eq_withDensity α β hs] at hX)

/-- The Radon–Nikodym derivative of a positive-scale stable law against Lebesgue measure is
`stablePDF`. -/
theorem rnDeriv_stableMeasure (α β : ℝ) (hs : 0 < s) (m : ℝ) :
    (stableMeasure α β s m).rnDeriv volume =ᵐ[volume] stablePDF α β s m := by
  rw [stableMeasure_eq_withDensity α β hs]
  exact Measure.rnDeriv_withDensity volume (measurable_stablePDF α β s m)

end TauCeti.Probability
