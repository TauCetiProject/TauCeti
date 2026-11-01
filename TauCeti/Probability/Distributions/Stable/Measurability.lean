/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Function.Sign
public import TauCeti.Probability.Distributions.Stable.PDF

/-!
# Parameter measurability of scalar stable laws

The scalar stable family is jointly Giry measurable in shape, skewness, scale, and location.
Thus measurable parameters give measurable measure-valued families for mixtures and kernels.
The characteristic exponent, characteristic function, and density are jointly measurable as
well, including the sample or frequency coordinate.

The density's definition as Fourier inversion of a jointly measurable characteristic function
(`stablePDFReal_def`) supplies its joint measurability for the whole totalized family.
Positive-scale laws inherit it through `withDensity`; at scale zero the valid laws are Dirac
measures, while invalid shapes give the zero measure at every scale. These identities cover the
full totalized family without asserting continuity across its invalid-parameter boundary.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
-/

public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal Real

namespace TauCeti.Probability

/-- The `S₀` characteristic exponent is jointly measurable in shape, skewness, and frequency,
including its explicit branches at shape one and frequency zero. -/
@[fun_prop]
theorem measurable_stableCharacteristicExponent :
    Measurable fun p : ℝ × ℝ × ℝ ↦ stableCharacteristicExponent p.1 p.2.1 p.2.2 := by
  -- The definition's body is hidden across module boundaries, so use its public branch lemmas.
  have hm : Measurable fun p : ℝ × ℝ × ℝ ↦
      if p.2.2 = 0 then (0 : ℂ)
      else if p.1 = 1 then
        (-|p.2.2| : ℂ) - (2 * p.2.1 / π * p.2.2 * Real.log |p.2.2| : ℝ) * I
      else (-|p.2.2| ^ p.1 : ℝ) +
        (p.2.1 * Real.tan (π * p.1 / 2) *
          (Real.sign p.2.2 * |p.2.2| ^ p.1 - p.2.2) : ℝ) * I := by
    refine Measurable.ite (by measurability) measurable_const ?_
    refine Measurable.ite (by measurability) (by fun_prop) ?_
    simp only [Real.tan_eq_sin_div_cos]
    fun_prop
  convert hm using 1
  funext p
  split_ifs with hu hα
  · simp [hu]
  · simp [hα, stableCharacteristicExponent_one]
  · exact stableCharacteristicExponent_of_ne_one_of_ne_zero hα _ hu

/-- The characteristic function of the totalized stable family is jointly measurable in all
parameters and the frequency, including invalid shapes and scale zero. -/
@[fun_prop]
theorem measurable_uncurry_charFun_stableMeasure :
    Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦
      charFun (stableMeasure p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2 := by
  have he : Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦
      stableCharacteristicExponent p.1 p.2.1 (p.2.2.1 * p.2.2.2.2) := by fun_prop
  have hm : Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦
      if p.1 ∈ Ioc 0 2 ∧ |p.2.1| ≤ 1 then
        cexp ((p.2.2.2.1 * p.2.2.2.2 : ℝ) * I +
          stableCharacteristicExponent p.1 p.2.1 (p.2.2.1 * p.2.2.2.2))
      else 0 := Measurable.ite (by measurability) (by fun_prop) measurable_const
  convert hm using 1
  funext p
  split_ifs with h
  · exact charFun_stableMeasure h.1 h.2 _ _ _
  · rw [stableMeasure_of_not_valid h, charFun_zero_measure]

/-- The stable density is jointly measurable in all parameters and the sample point. This
includes the zero density chosen at scale zero and at invalid shapes. -/
@[fun_prop]
theorem measurable_uncurry_stablePDFReal :
    Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦
      stablePDFReal p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have hc : Measurable fun p : (ℝ × ℝ × ℝ≥0 × ℝ × ℝ) × ℝ ↦
      charFun (stableMeasure p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1) p.2 :=
    measurable_uncurry_charFun_stableMeasure.comp
      (f := fun p : (ℝ × ℝ × ℝ≥0 × ℝ × ℝ) × ℝ ↦
        (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.2)) (by fun_prop)
  simpa only [stablePDFReal_def] using
    Measure.measurable_charFunDensity
      (x := fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦ p.2.2.2.2) hc (by fun_prop)

/-- The extended-real stable density is jointly measurable in all parameters and the sample
point. -/
@[fun_prop]
theorem measurable_uncurry_stablePDF :
    Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ × ℝ ↦
      stablePDF p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  simpa only [stablePDF_eq_ofReal] using measurable_uncurry_stablePDFReal.ennreal_ofReal

/-- The full totalized stable family is Giry measurable jointly in shape, skewness, scale,
and location. At valid shapes the zero-scale branch is Dirac; at invalid shapes it is zero. -/
@[fun_prop]
theorem measurable_stableMeasure :
    Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ ↦ stableMeasure p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hd : Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ ↦
      volume.withDensity (stablePDF p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    measurable_withDensity (measurable_uncurry_stablePDF.comp
      (f := fun p : (ℝ × ℝ × ℝ≥0 × ℝ) × ℝ ↦
        (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.2)) (by fun_prop))
  have hm : Measurable fun p : ℝ × ℝ × ℝ≥0 × ℝ ↦
      if p.2.2.1 = 0 then
        if p.1 ∈ Ioc 0 2 ∧ |p.2.1| ≤ 1 then Measure.dirac p.2.2.2 else 0
      else volume.withDensity (stablePDF p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    Measurable.ite (by measurability)
      (Measurable.ite (by measurability) (Measure.measurable_dirac.comp (by fun_prop))
        measurable_const) hd
  convert hm using 1
  funext p
  split_ifs with hs hv
  · simp only [hs, stableMeasure_zero_scale hv.1 hv.2]
  · rw [stableMeasure_of_not_valid hv]
  · exact stableMeasure_eq_withDensity _ _ (bot_lt_iff_ne_bot.mpr hs) _

end TauCeti.Probability
