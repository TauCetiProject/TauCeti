/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.GeneratingFunction
public import TauCeti.Probability.Quantile

/-!
# Distributional formulas for Dirac measures

This file records the cumulative mass of a Dirac measure on a preorder, the cumulative distribution
and the lower and upper quantile functions of a real Dirac measure, and the probability-generating
function, exponential-integrability domain and cumulant-generating function of a statistic under a
Dirac measure. The moment-generating function is already available in
Mathlib as `ProbabilityTheory.mgf_dirac'`.

## Main results

* `TauCeti.Probability.dirac_real_Iic` — the cumulative mass of a Dirac measure on a preorder;
* `TauCeti.Probability.cdf_dirac` — the cdf of a real Dirac measure;
* `TauCeti.Probability.pgf_dirac` — the probability-generating function of a natural-number-valued
  statistic under a Dirac measure;
* `MeasureTheory.Measure.quantile_dirac` and `MeasureTheory.Measure.upperQuantile_dirac` — the
  lower and upper quantile functions of a Dirac measure;
* `TauCeti.Probability.integrableExpSet_dirac` — every exponential moment exists under a Dirac
  measure;
* `TauCeti.Probability.cgf_dirac'` — the cumulant-generating function under a Dirac measure.
-/

public section

namespace TauCeti.Probability

open MeasureTheory ProbabilityTheory Set

/-- The cumulative mass of a Dirac measure is the indicator of the upper set of its atom. -/
theorem dirac_real_Iic {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Preorder α]
    (a b : α) [Decidable (a ≤ b)] :
    (Measure.dirac a).real (Iic b) = if a ≤ b then 1 else 0 := by
  by_cases h : a ≤ b <;> simp [Measure.dirac_real_apply, Set.indicator, h]

/-- The cumulative distribution function of a Dirac measure is a step function. -/
@[simp]
theorem cdf_dirac (a x : ℝ) : cdf (Measure.dirac a) x = if a ≤ x then 1 else 0 := by
  rw [cdf_eq_real, dirac_real_Iic]

/-- The probability-generating function of a natural-number-valued statistic under a Dirac
measure is a monomial. -/
@[simp]
theorem pgf_dirac {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (X : Ω → ℕ)
    (ω : Ω) (z : ℝ) : pgf X (Measure.dirac ω) z = z ^ X ω := by
  simp [pgf_def]

/-- Every exponential moment of a Dirac measure exists. -/
@[simp]
theorem integrableExpSet_dirac {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (X : Ω → ℝ) (ω : Ω) :
    integrableExpSet X (Measure.dirac ω) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_dirac (by simp)

/-- The cumulant-generating function of a Dirac measure is linear. -/
@[simp]
theorem cgf_dirac' {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (X : Ω → ℝ) (ω : Ω) (t : ℝ) :
    cgf X (Measure.dirac ω) t = t * X ω := by
  rw [cgf, mgf_dirac', Real.log_exp]

end TauCeti.Probability

namespace MeasureTheory.Measure

open ProbabilityTheory Set TauCeti.Probability

/-- At every level in `Ioc 0 1`, including the endpoint level `1`, the quantile function of a
Dirac law is its atom. -/
@[simp]
theorem quantile_dirac (a : ℝ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : (dirac a).quantile t = a := by
  rw [quantile_def]
  refine le_antisymm (csInf_le (bddBelow_setOf_le_cdf (dirac a) h0) ?_)
    (le_csInf ⟨a, ?_⟩ fun x hx ↦ ?_)
  · simpa [TauCeti.Probability.cdf_dirac] using h1
  · simpa [TauCeti.Probability.cdf_dirac] using h1
  · by_contra hxa
    exact absurd hx (by simpa [TauCeti.Probability.cdf_dirac, not_le.mpr (not_le.mp hxa)] using h0)

/-- At every level in `Ico 0 1`, including the endpoint level `0`, the upper quantile function of
a Dirac law is its atom. -/
@[simp]
theorem upperQuantile_dirac (a : ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    (dirac a).upperQuantile t = a := by
  have hset : {x : ℝ | t < cdf (dirac a) x} = Ici a := by
    ext x
    by_cases hx : a ≤ x <;> simp [hx, h1, h0]
  rw [upperQuantile_def, hset, csInf_Ici]

/-- At every level, including those outside `Ioc 0 1` where the junk values of the quantile
function apply, the quantile function of the Dirac law at `0` is `0`. -/
@[simp]
theorem quantile_dirac_zero (t : ℝ) : (dirac (0 : ℝ)).quantile t = 0 := by
  rcases le_or_gt t 0 with h0 | h0
  · exact quantile_of_nonpos _ h0
  rcases le_or_gt t 1 with h1 | h1
  · exact quantile_dirac 0 h0 h1
  · exact quantile_of_one_lt _ h1

end MeasureTheory.Measure
