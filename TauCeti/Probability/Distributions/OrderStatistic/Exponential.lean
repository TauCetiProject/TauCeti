/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Data.Fin.Tuple.OrderStatistic
import TauCeti.Probability.Distributions.Exponential.Basic
import TauCeti.Probability.Distributions.OrderStatistic.Independent

/-!
# Exponential laws of least order statistics

Because `orderStatistic 0` of a nonempty finite tuple coincides with its sample minimum
(`TauCeti.Probability.map_orderStatistic_zero`), the additive-rate closure of independent
exponential minima transfers directly to the least order statistic `orderStatistic 0`.

## Main results

* `TauCeti.Probability.map_orderStatistic_zero_pi_expMeasure` — pushforward law of
  `orderStatistic 0` under a nonempty finite product of exponential laws with positive rates `r i`;
* `TauCeti.Probability.hasLaw_orderStatistic_zero_indep_expMeasure` — `HasLaw` form for independent
  heterogeneous exponential coordinates, with no explicit positivity hypothesis on the rates.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §§2.3 and 5.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {n : ℕ}

/-- The least order statistic of `n ≠ 0` independent exponential coordinates with positive rates
`r i` has law `expMeasure (∑ i, r i)`. -/
theorem map_orderStatistic_zero_pi_expMeasure [NeZero n] {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    (Measure.pi fun i ↦ expMeasure (r i)).map (orderStatistic 0) =
      expMeasure (∑ i, r i) := by
  rw [map_orderStatistic_zero, map_min_pi_expMeasure hr]

/-- Random-variable form of `TauCeti.Probability.map_orderStatistic_zero_pi_expMeasure`: the least
order statistic of `n ≠ 0` independent exponential variables with rates `r i` has law
`expMeasure (∑ i, r i)`, with no explicit positivity hypothesis on `r`. -/
theorem hasLaw_orderStatistic_zero_indep_expMeasure {Ω : Type*} {_ : MeasurableSpace Ω} [NeZero n]
    {P : Measure Ω} {r : Fin n → ℝ} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (expMeasure (r i)) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) (expMeasure (∑ i, r i)) P := by
  simp_rw [orderStatistic_zero]
  exact hasLaw_min_indep_expMeasure hindep hX

end TauCeti.Probability
