/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Quantile
public import TauCeti.Probability.Distributions.Levy.Transforms
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Levy.Gaussian
import TauCeti.Probability.Distributions.Levy.Moments
import TauCeti.Probability.Quantile.Map

/-!
# Reflected Lévy laws

Reflecting a Lévy variable with location `m` and scale `c > 0` gives a law carried by the
half-line `(-∞, -m)`. It is the law of every negative-slope affine image of a Lévy variable, and
the law of `-m - c / Z ^ 2` for a standard Gaussian `Z`. Its cdf is

`erf (√(c / (2 (-x - m))))`

below `-m` and one from `-m` on, and its interior quantile is `-m - c / (2 * erfInv u ^ 2)`, that
is `-m - c / z((1 + u) / 2) ^ 2` in terms of the standard Gaussian quantile `z`. Its exponential
moments exist exactly at `t ≥ 0`, where the moment-generating function is
`exp (-m t - √(2 c t))`.

The measure is kept as the reflection of `levyMeasure`; no parallel family definition is needed.

## Main results

* `TauCeti.Probability.map_affine_levyMeasure_of_neg` identifies a negative-slope affine image as
  a reflected Lévy law, with the random-variable form
  `TauCeti.Probability.hasLaw_affine_levyMeasure_of_neg`;
* `TauCeti.Probability.gaussianReal_map_neg_sub_div_sq` and
  `TauCeti.Probability.hasLaw_neg_levyMeasure_of_hasLaw_gaussianReal` give the Gaussian
  construction;
* `TauCeti.Probability.cdf_neg_levyMeasure_eq` computes the cdf;
* `TauCeti.Probability.quantile_neg_levyMeasure` and
  `TauCeti.Probability.quantile_neg_levyMeasure_eq_quantile_gaussianReal` compute the interior
  quantile, with endpoint limits `TauCeti.Probability.tendsto_quantile_neg_levyMeasure_nhdsGT_zero`
  and `TauCeti.Probability.tendsto_quantile_neg_levyMeasure_nhdsLT_one`;
* `TauCeti.Probability.integrableExpSet_id_neg_levyMeasure`,
  `TauCeti.Probability.mgf_id_neg_levyMeasure` and `TauCeti.Probability.cgf_id_neg_levyMeasure`
  give the exact exponential-integrability domain and the transforms on it.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer (2020),
  chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {m c u t : ℝ}

/-- **Negative affine transport.** For `b < 0`, the law of `a + b X` for a Lévy variable `X` with
location `m` and scale `c` is the reflection of the Lévy law with location `-a + -b * m` and scale
`-b * c`. The identity also respects the nonpositive-scale zero-measure branch. -/
theorem map_affine_levyMeasure_of_neg {b : ℝ} (hb : b < 0) (a m c : ℝ) :
    (levyMeasure m c).map (fun x ↦ a + b * x) = (levyMeasure (-a + -b * m) (-b * c)).neg := by
  rw [← map_affine_levyMeasure (neg_pos.mpr hb), neg_map_affine, neg_neg, neg_neg]

/-- The random-variable form of negative affine transport of the Lévy law. -/
theorem hasLaw_affine_levyMeasure_of_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {b : ℝ} (hb : b < 0) (a : ℝ) (hX : HasLaw X (levyMeasure m c) P) :
    HasLaw (fun ω ↦ a + b * X ω) (levyMeasure (-a + -b * m) (-b * c)).neg P := by
  rw [← map_affine_levyMeasure_of_neg hb]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ ↦ a + b * x).aemeasurable).comp hX

/-- **The Gaussian construction of the reflected Lévy law.** If `Z` is standard Gaussian and
`c > 0`, then `-m - c / Z ^ 2` has the reflected Lévy law with location `m` and scale `c`. -/
theorem gaussianReal_map_neg_sub_div_sq (hc : 0 < c) (m : ℝ) :
    (gaussianReal 0 1).map (fun z ↦ -m - c / z ^ 2) = (levyMeasure m c).neg := by
  rw [← gaussianReal_map_add_div_sq hc m, Measure.neg_def,
    Measure.map_map measurable_neg (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply]
  ring

/-- The random-variable form of the Gaussian construction of the reflected Lévy law. -/
theorem hasLaw_neg_levyMeasure_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} (hc : 0 < c) (m : ℝ) (hZ : HasLaw Z (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ -m - c / Z ω ^ 2) (levyMeasure m c).neg P :=
  (HasLaw.mk (by fun_prop) (gaussianReal_map_neg_sub_div_sq hc m)).comp hZ

/-- **The cdf of a reflected Lévy law** with positive scale is `erf (√(c / (2 (-x - m))))` below
the reflected location `-m` and one from `-m` on. -/
theorem cdf_neg_levyMeasure_eq (hc : 0 < c) (m x : ℝ) :
    cdf (levyMeasure m c).neg x = if -m ≤ x then 1 else Real.erf (√(c / (2 * (-x - m)))) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  have hsingleton : levyMeasure m c {-x} = 0 := by
    rw [levyMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
  rw [Measure.cdf_neg_of_measure_singleton_eq_zero hsingleton, cdf_levyMeasure_eq hc]
  by_cases hx : -m ≤ x
  · rw [ite_eq_left (by linarith : -x ≤ m), ite_eq_left hx, sub_zero]
  · rw [ite_eq_right (by linarith : ¬-x ≤ m), ite_eq_right hx, Real.erfc_def, sub_sub_cancel]

/-- The quantile of a reflected Lévy law with location `m` and positive scale `c` at an interior
level `u` is `-m - c / (2 * erfInv u ^ 2)`. -/
theorem quantile_neg_levyMeasure (hc : 0 < c) (m : ℝ) (hu : u ∈ Ioo 0 1) :
    (levyMeasure m c).neg.quantile u = -m - c / (2 * Real.erfInv u ^ 2) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  have hu' : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [Measure.quantile_neg_of_continuousWithinAt hu.1 hu.2
      ((continuousOn_quantile_levyMeasure hc m).continuousAt
        (Ioo_mem_nhds hu'.1 hu'.2)).continuousWithinAt,
    quantile_levyMeasure hc m hu', sub_sub_cancel, neg_add']

/-- The reflected Lévy quantile in terms of the standard Gaussian quantile `z`: at an interior
level `u` it is `-m - c / z((1 + u) / 2) ^ 2`. -/
theorem quantile_neg_levyMeasure_eq_quantile_gaussianReal (hc : 0 < c) (m : ℝ)
    (hu : u ∈ Ioo 0 1) :
    (levyMeasure m c).neg.quantile u =
      -m - c / (gaussianReal 0 1).quantile ((1 + u) / 2) ^ 2 := by
  have hp : (1 + u) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [quantile_neg_levyMeasure hc m hu, quantile_gaussianReal_zero_one hp, mul_pow,
    Real.sq_sqrt zero_le_two]
  ring_nf

/-- The reflected Lévy quantile tends to `-∞` as the level tends to `0` from above. -/
theorem tendsto_quantile_neg_levyMeasure_nhdsGT_zero (hc : 0 < c) (m : ℝ) :
    Tendsto (fun u ↦ ((levyMeasure m c).neg.quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  simpa using
    Measure.tendsto_quantile_neg_nhdsGT_zero (tendsto_quantile_levyMeasure_nhdsLT_one hc m)

/-- The reflected Lévy quantile tends to the reflected location `-m` as the level tends to `1`
from below. -/
theorem tendsto_quantile_neg_levyMeasure_nhdsLT_one (hc : 0 < c) (m : ℝ) :
    Tendsto (fun u ↦ ((levyMeasure m c).neg.quantile u : EReal)) (𝓝[<] 1)
      (𝓝 ((-m : ℝ) : EReal)) := by
  let _ := isProbabilityMeasure_levyMeasure hc m
  have h := Measure.tendsto_quantile_neg_nhdsLT_one (tendsto_quantile_levyMeasure_nhdsGT_zero hc m)
  rwa [← EReal.coe_neg] at h

/-- **The exact exponential-integrability domain of a reflected Lévy law** with positive scale is
the nonnegative half-line. -/
@[simp]
theorem integrableExpSet_id_neg_levyMeasure (hc : 0 < c) (m : ℝ) :
    integrableExpSet id (levyMeasure m c).neg = Ici 0 := by
  rw [integrableExpSet_id_neg, integrableExpSet_id_levyMeasure hc]
  ext t
  simp

/-- **The moment-generating function of a reflected Lévy law** with location `m` and positive
scale `c` is `exp (-m t - √(2 c t))` on its exponential-integrability domain `t ≥ 0`. -/
theorem mgf_id_neg_levyMeasure (hc : 0 < c) (m : ℝ) (ht : 0 ≤ t) :
    mgf id (levyMeasure m c).neg t = exp (-m * t - √(2 * c * t)) := by
  rw [mgf_id_neg, mgf_id_levyMeasure hc m (by linarith), show -2 * c * -t = 2 * c * t by ring,
    neg_mul_comm]

/-- **The cumulant-generating function of a reflected Lévy law** with location `m` and positive
scale `c` is `-m t - √(2 c t)` on its exponential-integrability domain `t ≥ 0`. -/
theorem cgf_id_neg_levyMeasure (hc : 0 < c) (m : ℝ) (ht : 0 ≤ t) :
    cgf id (levyMeasure m c).neg t = -m * t - √(2 * c * t) := by
  rw [cgf, mgf_id_neg_levyMeasure hc m ht, log_exp]

end TauCeti.Probability
