/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import TauCeti.Probability.Distributions.Levy.CharFun

/-!
# Lévy specializations of scalar stable laws

The fully right-skewed stable law of shape one half and positive scale `s` is the Lévy law
with location `m - s` and scale `s`. The location correction is required by Nolan's `S₀`
convention. Full left skewness gives the reflection of a Lévy law with location `-m - s`.
The identities connect the stable characteristic-function construction with the
inverse-gamma construction of the Lévy law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

private theorem stableCharacteristicExponent_one_half_one (u : ℝ) :
    stableCharacteristicExponent 2⁻¹ 1 u =
      -Complex.sqrt (-2 * Complex.I * u) - (u : ℂ) * Complex.I := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have htan : tan (π * 2⁻¹ / 2) = 1 := by
    convert tan_pi_div_four using 1; congr 1; ring
  have hnorm : ‖-2 * Complex.I * (u : ℂ)‖ = 2 * |u| := by
    simp
  have hre : (-2 * Complex.I * (u : ℂ)).re = 0 := by simp
  have him : (-2 * Complex.I * (u : ℂ)).im = -2 * u := by simp
  have hdiv : 2 * |u| / 2 = |u| := by ring
  rw [stableCharacteristicExponent_of_ne_one_of_ne_zero (by norm_num) 1 hu,
    htan, ← one_div (2 : ℝ), ← sqrt_eq_rpow, Complex.sqrt_eq_real_add_ite, hnorm, hre, him,
    add_zero, sub_zero, hdiv]
  simp only [one_mul]
  rcases hu.lt_or_gt with hu | hu
  · rw [sign_of_neg hu, ite_eq_left (by linarith : 0 ≤ -2 * u)]
    push_cast
    ring
  · rw [sign_of_pos hu, ite_eq_right (by linarith : ¬0 ≤ -2 * u)]
    push_cast
    ring

/-- A fully right-skewed stable law of shape one half is a Lévy law. Its location is
`m - s`, rather than `m`, in Nolan's `S₀` convention. -/
@[simp]
theorem stableMeasure_one_half_one {s : ℝ≥0} (hs : 0 < s) (m : ℝ) :
    stableMeasure 2⁻¹ 1 s m = levyMeasure (m - s) s := by
  let _ := isProbabilityMeasure_levyMeasure (NNReal.coe_pos.mpr hs) (m - s)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stableMeasure (by norm_num) (by norm_num),
    charFun_levyMeasure (NNReal.coe_pos.mpr hs), stableCharacteristicExponent_one_half_one]
  congr 1
  push_cast
  ring_nf

/-- A fully left-skewed stable law of shape one half is the reflection of a Lévy law. -/
@[simp]
theorem stableMeasure_one_half_neg_one {s : ℝ≥0} (hs : 0 < s) (m : ℝ) :
    stableMeasure 2⁻¹ (-1) s m = (levyMeasure (-m - s) s).map Neg.neg := by
  let _ := isProbabilityMeasure_levyMeasure (NNReal.coe_pos.mpr hs) (-m - s)
  apply Measure.ext_of_charFun
  funext t
  have hmap : charFun ((levyMeasure (-m - s) s).map Neg.neg) t =
      charFun (levyMeasure (-m - s) s) (-t) := by
    simpa only [neg_one_mul] using
      (charFun_map_mul (μ := levyMeasure (-m - s) s) (-1) t)
  rw [hmap, charFun_levyMeasure (NNReal.coe_pos.mpr hs),
    charFun_stableMeasure (by norm_num) (by norm_num),
    stableCharacteristicExponent_neg_skew, stableCharacteristicExponent_one_half_one]
  congr 1
  push_cast
  ring_nf

end TauCeti.Probability
