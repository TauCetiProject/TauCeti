/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
import TauCeti.Probability.Distributions.Gumbel.PDF
import TauCeti.Probability.Quantile.Map

/-!
# Minimum Gumbel laws by reflection

Reflecting a maximum-convention Gumbel variable produces the minimum convention. If
`X` has location `m` and scale `s`, then `-X` has cdf

`1 - exp (-exp ((x + m) / s))`

and quantile `-m + s * log (-log (1 - u))`. Thus the reflected location is `-m`.
The measure is kept as the reflection of `gumbelMeasure`; no parallel family definition is
needed.

## Main results

* `TauCeti.Probability.gumbelMeasure_map_neg` identifies the reflected law as an exponential
  pushforward, with the random-variable form
  `TauCeti.Probability.hasLaw_neg_gumbelMeasure_of_hasLaw_expMeasure`;
* `TauCeti.Probability.cdf_neg_gumbelMeasure_eq` computes the cdf;
* `TauCeti.Probability.quantile_neg_gumbelMeasure` computes the interior quantile;
* `TauCeti.Probability.tendsto_quantile_neg_gumbelMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_neg_gumbelMeasure_nhdsLT_one` give the one-sided
  endpoint limits of the quantile.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 22.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

open scoped ENNReal Topology

namespace TauCeti.Probability

variable {m s u x : ℝ}

/-- Reflecting a positive-scale Gumbel law gives the image of a rate-one exponential variable
under `e ↦ -m + s * log e`, the minimum-Gumbel construction. -/
theorem gumbelMeasure_map_neg (hs : 0 < s) (m : ℝ) :
    (gumbelMeasure m s).neg =
      (expMeasure 1).map fun e => -m + s * Real.log e := by
  rw [Measure.neg_def, gumbelMeasure_of_pos hs, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext e
  simp only [Function.comp_apply]
  ring

/-- If `E` has the rate-one exponential law, then `-m + s * log E` has the reflected Gumbel
law. -/
theorem hasLaw_neg_gumbelMeasure_of_hasLaw_expMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {E : Ω → ℝ} (hs : 0 < s) (m : ℝ)
    (hE : HasLaw E (expMeasure 1) P) :
    HasLaw (fun ω => -m + s * Real.log (E ω)) (gumbelMeasure m s).neg P := by
  rw [gumbelMeasure_map_neg hs]
  exact (hasLaw_map
    (measurable_const.add (measurable_const.mul Real.measurable_log)).aemeasurable).comp hE

/-- The cdf of the reflected positive-scale Gumbel law, in the minimum convention. -/
theorem cdf_neg_gumbelMeasure_eq (hs : 0 < s) (m x : ℝ) :
    cdf (gumbelMeasure m s).neg x =
      1 - Real.exp (-Real.exp ((x + m) / s)) := by
  let _ : IsProbabilityMeasure (gumbelMeasure m s) :=
    isProbabilityMeasure_gumbelMeasure hs m
  have hsingleton : gumbelMeasure m s {-x} = 0 := by
    rw [gumbelMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
  rw [Measure.cdf_neg_of_measure_singleton_eq_zero hsingleton, cdf_gumbelMeasure_eq hs,
    show -((-x - m) / s) = (x + m) / s by ring]

/-- The interior quantile of the reflected positive-scale Gumbel law. This is the
minimum-convention formula with reflected location `-m`. -/
theorem quantile_neg_gumbelMeasure (hs : 0 < s) (m : ℝ) (hu : u ∈ Ioo 0 1) :
    (gumbelMeasure m s).neg.quantile u =
      -m + s * Real.log (-Real.log (1 - u)) := by
  let _ : IsProbabilityMeasure (gumbelMeasure m s) :=
    isProbabilityMeasure_gumbelMeasure hs m
  rw [Measure.quantile_neg hu.1 hu.2,
    upperQuantile_gumbelMeasure hs m ⟨sub_pos.mpr hu.2, sub_lt_self 1 hu.1⟩]
  ring

/-- Reflected Gumbel quantiles tend to the lower endpoint `-∞` as the level tends to zero
from above. -/
theorem tendsto_quantile_neg_gumbelMeasure_nhdsGT_zero (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((gumbelMeasure m s).neg.quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  apply Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos
  intro x
  rw [cdf_neg_gumbelMeasure_eq hs]
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _)))

/-- Reflected Gumbel quantiles tend to the upper endpoint `+∞` as the level tends to one
from below. -/
theorem tendsto_quantile_neg_gumbelMeasure_nhdsLT_one (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((gumbelMeasure m s).neg.quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one
  intro x
  rw [cdf_neg_gumbelMeasure_eq hs]
  exact sub_lt_self 1 (Real.exp_pos _)

end TauCeti.Probability
