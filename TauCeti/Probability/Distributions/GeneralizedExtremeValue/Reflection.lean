/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Quantile
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.GeneralizedExtremeValue.PDF
import TauCeti.Probability.Quantile.Map

/-!
# Minimum-convention generalized extreme-value laws by reflection

Reflecting a maximum-convention generalized extreme-value variable gives the minimum convention,
which is the law of every negative-slope affine image. If `X` has location `m`, scale `s > 0` and
nonzero shape `ξ`, then `-X` has cdf

`1 - exp (-(1 - ξ * ((x + m) / s)) ^ (-1 / ξ))`

where `1 - ξ * ((x + m) / s) > 0`, extended by one beyond a finite upper endpoint (`ξ > 0`) and by
zero below a finite lower endpoint (`ξ < 0`). Its interior quantile is
`-m - s * ((-log (1 - u)) ^ (-ξ) - 1) / ξ`, with the reflected Gumbel expression at shape zero.
The finite endpoint of the reflected law is `s / ξ - m`, the reflection of the finite endpoint
`m - s / ξ` of the maximum-convention law.

The measure is kept as the reflection of `generalizedExtremeValueMeasure`; no parallel family
definition is needed. At shape zero it is the reflected Gumbel law of
`TauCeti.Probability.Distributions.Gumbel.Reflection`, by `generalizedExtremeValueMeasure_zero`.

## Main results

* `TauCeti.Probability.map_affine_generalizedExtremeValueMeasure_of_neg` identifies a
  negative-slope affine image as a reflected law, with the random-variable form
  `TauCeti.Probability.hasLaw_affine_generalizedExtremeValueMeasure_of_neg`;
* `TauCeti.Probability.hasLaw_neg_generalizedExtremeValueMeasure_of_hasLaw_expMeasure` gives the
  minimum-convention construction from a rate-one exponential variable;
* `TauCeti.Probability.cdf_neg_generalizedExtremeValueMeasure_eq` computes the cdf at nonzero
  shape;
* `TauCeti.Probability.quantile_neg_generalizedExtremeValueMeasure` computes the interior
  quantile;
* the `tendsto_quantile_neg_generalizedExtremeValueMeasure_*` lemmas give the one-sided endpoint
  limits of the quantile for positive and negative shape.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Section 3.1.4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {s ξ u : ℝ}

/-- **Negative affine transport.** For `b < 0`, the law of `a + b X` for a generalized
extreme-value variable `X` with location `m`, scale `s` and shape `ξ` is the reflection of the
generalized extreme-value law with location `-a + -b * m`, scale `-b * s` and the same shape. The
identity also respects the nonpositive-scale zero-measure branch. -/
theorem map_affine_generalizedExtremeValueMeasure_of_neg {b : ℝ} (hb : b < 0) (a m s ξ : ℝ) :
    (generalizedExtremeValueMeasure m s ξ).map (fun x => a + b * x) =
      (generalizedExtremeValueMeasure (-a + -b * m) (-b * s) ξ).neg := by
  rw [← map_affine_generalizedExtremeValueMeasure (neg_pos.mpr hb), neg_map_affine, neg_neg,
    neg_neg]

/-- The random-variable form of negative affine transport of generalized extreme-value laws. -/
theorem hasLaw_affine_generalizedExtremeValueMeasure_of_neg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m b : ℝ} (hb : b < 0) (a : ℝ)
    (hX : HasLaw X (generalizedExtremeValueMeasure m s ξ) P) :
    HasLaw (fun ω => a + b * X ω)
      (generalizedExtremeValueMeasure (-a + -b * m) (-b * s) ξ).neg P := by
  rw [← map_affine_generalizedExtremeValueMeasure_of_neg hb]
  exact (hasLaw_map (by fun_prop : Measurable (fun x : ℝ => a + b * x)).aemeasurable).comp hX

/-- If `E` has the rate-one exponential law, then the negated generalized extreme-value
transformation of `E` has the reflected generalized extreme-value law. -/
theorem hasLaw_neg_generalizedExtremeValueMeasure_of_hasLaw_expMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℝ}
    (hs : 0 < s) (m ξ : ℝ) (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => -generalizedExtremeValueMap m s ξ (E ω))
      (generalizedExtremeValueMeasure m s ξ).neg P := by
  rw [Measure.neg_def]
  exact (hasLaw_map measurable_neg.aemeasurable).comp
    (hasLaw_generalizedExtremeValueMeasure_of_hasLaw_expMeasure hs m ξ hE)

/-- The cdf of the reflected positive-scale, nonzero-shape generalized extreme-value law, in the
minimum convention. The formula includes the one or zero extension beyond its finite support
endpoint `s / ξ - m`. -/
theorem cdf_neg_generalizedExtremeValueMeasure_eq (hs : 0 < s) (hξ : ξ ≠ 0) (m x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s ξ).neg x =
      if 0 < 1 - ξ * ((x + m) / s) then
        1 - exp (-((1 - ξ * ((x + m) / s)) ^ (-1 / ξ)))
      else if 0 < ξ then 1 else 0 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have hsingleton : generalizedExtremeValueMeasure m s ξ {-x} = 0 := by
    rw [generalizedExtremeValueMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
  rw [Measure.cdf_neg_of_measure_singleton_eq_zero hsingleton,
    cdf_generalizedExtremeValueMeasure_eq hs hξ,
    show 1 + ξ * ((-x - m) / s) = 1 - ξ * ((x + m) / s) by ring]
  split_ifs <;> ring

/-- The interior quantile of the reflected positive-scale generalized extreme-value law, including
the reflected Gumbel expression at shape zero. -/
theorem quantile_neg_generalizedExtremeValueMeasure (m ξ : ℝ) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (generalizedExtremeValueMeasure m s ξ).neg.quantile u =
      if ξ = 0 then -m + s * log (-log (1 - u))
      else -m - s * ((-log (1 - u)) ^ (-ξ) - 1) / ξ := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have hu' : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [Measure.quantile_neg_of_continuousWithinAt hu.1 hu.2
      ((continuousOn_quantile_generalizedExtremeValueMeasure hs m ξ).continuousAt
        (Ioo_mem_nhds hu'.1 hu'.2)).continuousWithinAt,
    quantile_generalizedExtremeValueMeasure m ξ hs hu']
  split_ifs <;> ring

/-- For positive shape, reflected generalized extreme-value quantiles tend to minus infinity as
the level tends to zero from above. -/
theorem tendsto_quantile_neg_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_pos
    (hs : 0 < s) (m : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).neg.quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  simpa using Measure.tendsto_quantile_neg_nhdsGT_zero
    (tendsto_quantile_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_pos hs m hξ)

/-- For negative shape, reflected generalized extreme-value quantiles tend to the finite lower
endpoint `s / ξ - m` as the level tends to zero from above. -/
theorem tendsto_quantile_neg_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_neg
    (hs : 0 < s) (m : ℝ) (hξ : ξ < 0) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).neg.quantile u : EReal))
      (𝓝[>] 0) (𝓝 ((s / ξ - m : ℝ) : EReal)) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have h := Measure.tendsto_quantile_neg_nhdsGT_zero
    (tendsto_quantile_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_neg hs m hξ)
  rwa [← EReal.coe_div, ← EReal.coe_sub, ← EReal.coe_neg, neg_sub] at h

/-- For positive shape, reflected generalized extreme-value quantiles tend to the finite upper
endpoint `s / ξ - m` as the level tends to one from below. -/
theorem tendsto_quantile_neg_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_pos
    (hs : 0 < s) (m : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).neg.quantile u : EReal))
      (𝓝[<] 1) (𝓝 ((s / ξ - m : ℝ) : EReal)) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have h := Measure.tendsto_quantile_neg_nhdsLT_one
    (tendsto_quantile_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_pos hs m hξ)
  rwa [← EReal.coe_div, ← EReal.coe_sub, ← EReal.coe_neg, neg_sub] at h

/-- For negative shape, reflected generalized extreme-value quantiles tend to plus infinity as the
level tends to one from below. -/
theorem tendsto_quantile_neg_generalizedExtremeValueMeasure_nhdsLT_one_of_shape_neg
    (hs : 0 < s) (m : ℝ) (hξ : ξ < 0) :
    Tendsto (fun u ↦ ((generalizedExtremeValueMeasure m s ξ).neg.quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  simpa using Measure.tendsto_quantile_neg_nhdsLT_one
    (tendsto_quantile_generalizedExtremeValueMeasure_nhdsGT_zero_of_shape_neg hs m hξ)

end TauCeti.Probability
