/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.StochasticOrder

/-!
# Stochastic comparison of Poisson laws

Increasing the nonnegative rate makes a Poisson variable stochastically larger. The comparison
comes from adding an independent Poisson increment whose rate is the difference of the two rates.
This construction includes equal rates and the rate-zero boundary.

The resulting reversed cdf inequality gives ordered interior quantiles and an almost surely
ordered common-uniform quantile coupling. Its marginals are the two real-cast Poisson laws by
`MeasureTheory.Measure.isCoupling_quantileCoupling`.

## Main results

* `cdf_map_cast_poissonMeasure_le`: cdfs decrease as the rate increases.
* `quantile_map_cast_poissonMeasure_le`: interior quantiles increase with the rate.
* `ae_fst_le_snd_quantileCoupling_map_cast_poissonMeasure`: the common-uniform ordered coupling.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 4.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {r s : ℝ≥0} {u : ℝ}

/-- Increasing the rate decreases the cdf of a real-cast Poisson law. -/
theorem cdf_map_cast_poissonMeasure_le (hrs : r ≤ s) (x : ℝ) :
    cdf Po(ℝ, s) x ≤ cdf Po(ℝ, r) x := by
  let P := Po(r).prod Po(s - r)
  have hfst : HasLaw Prod.fst Po(r) P := measurePreserving_fst.hasLaw
  have hsnd : HasLaw Prod.snd Po(s - r) P := measurePreserving_snd.hasLaw
  have hindep : IndepFun Prod.fst Prod.snd P :=
    (indepFun_iff_hasLaw_prodMk_prod hfst hsnd).2 HasLaw.id
  have hsum : HasLaw (fun z : ℕ × ℕ ↦ z.1 + z.2) Po(s) P := by
    simpa only [poissonMeasure_conv_poissonMeasure, add_tsub_cancel_of_le hrs] using
      hindep.hasLaw_fun_add hfst hsnd
  have hcast (t : ℝ≥0) : HasLaw (Nat.cast : ℕ → ℝ) Po(ℝ, t) Po(t) :=
    hasLaw_map (by fun_prop)
  apply ((hcast r).comp hfst).cdf_le_of_ae_le ((hcast s).comp hsum) _ x
  exact ae_of_all _ fun z ↦ Nat.cast_le.mpr (Nat.le_add_right z.1 z.2)

/-- Interior quantiles of real-cast Poisson laws increase with the rate. -/
theorem quantile_map_cast_poissonMeasure_le (hrs : r ≤ s) (hu : u ∈ Set.Ioo 0 1) :
    Po(ℝ, r).quantile u ≤ Po(ℝ, s).quantile u :=
  (Measure.cdf_le_iff_quantile_le _ _).1 (cdf_map_cast_poissonMeasure_le hrs) u hu.1 hu.2

/-- The common-uniform quantile coupling of real-cast Poisson laws is almost surely ordered when
the rate increases. Its marginals are given by `Measure.isCoupling_quantileCoupling`. -/
theorem ae_fst_le_snd_quantileCoupling_map_cast_poissonMeasure (hrs : r ≤ s) :
    ∀ᵐ z ∂Po(ℝ, r).quantileCoupling Po(ℝ, s), z.1 ≤ z.2 :=
  Measure.ae_fst_le_snd_quantileCoupling _ _ (cdf_map_cast_poissonMeasure_le hrs)

end TauCeti.Probability
