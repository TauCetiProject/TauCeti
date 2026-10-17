/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.Probability.Quantile

/-!
# Interval truncation of real probability laws

Conditioning a real probability law `μ` on the interval `(l, r]` retains precisely the
cumulative mass between the two endpoints and renormalizes it. This file computes the resulting
cumulative distribution function and quantile. The formulas retain atoms at the upper endpoint
and exclude atoms at the lower endpoint, in accordance with the choice of `Set.Ioc l r`.

If `L = cdf μ l` and `R = cdf μ r`, the conditional cdf is the clipped increment

```text
(min R (max L (cdf μ x)) - L) / (R - L).
```

Consequently, at an interior level `u`, its quantile is the quantile of `μ` at the rescaled level
`L + u * (R - L)`. The strict hypothesis `L < R` says exactly that the conditioning interval has
positive mass and ensures that both conditional laws and quantiles are nondegenerate.

## Main results

* `MeasureTheory.Measure.cdf_cond` — the cdf of a law conditioned on a measurable event;
* `MeasureTheory.Measure.cdf_cond_Ioc` — the cdf of a law conditioned on `(l, r]`;
* `MeasureTheory.Measure.quantile_cond_Ioc` — the corresponding interior quantile formula.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- The cdf of `μ` conditioned on a measurable event is the proportion of that event lying below
the cdf argument. -/
theorem cdf_cond [IsFiniteMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (hμA : μ A ≠ 0)
    (x : ℝ) :
    cdf (ProbabilityTheory.cond μ A) x = μ.real (A ∩ Iic x) / μ.real A := by
  have := ProbabilityTheory.cond_isProbabilityMeasure hμA
  simp [cdf_eq_real, measureReal_def, ProbabilityTheory.cond_apply hA, div_eq_inv_mul]

variable [IsProbabilityMeasure μ]

/-- The cdf of `μ` conditioned on `(l, r]` is the increment of the original cdf above `cdf μ l`,
clipped between the endpoint masses and normalized by `cdf μ r - cdf μ l`. -/
theorem cdf_cond_Ioc {l r : ℝ} (hLR : cdf μ l < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioc l r)) x =
      (min (cdf μ r) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (cdf μ r - cdf μ l) := by
  have hlr : l < r := (monotone_cdf μ).reflect_lt hLR
  have hmass : μ (Ioc l r) ≠ 0 := (measure_Ioc_pos_iff_cdf_lt μ).2 hLR |>.ne'
  rw [cdf_cond μ measurableSet_Ioc hmass, measureReal_Ioc_eq_cdf_sub μ hlr.le]
  by_cases hxl : x ≤ l
  · have hinter : Ioc l r ∩ Iic x = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_empty_iff_false, iff_false]
      grind
    rw [hinter, measureReal_empty]
    have hFxL : cdf μ x ≤ cdf μ l := monotone_cdf μ hxl
    rw [max_eq_left hFxL, min_eq_right hLR.le, sub_self, zero_div]
  · have hlx : l ≤ x := (not_le.mp hxl).le
    by_cases hxr : x ≤ r
    · have hinter : Ioc l r ∩ Iic x = Ioc l x := by
        ext y
        simp only [mem_inter_iff, mem_Ioc, mem_Iic]
        grind
      rw [hinter, measureReal_Ioc_eq_cdf_sub μ hlx,
        max_eq_right (monotone_cdf μ hlx), min_eq_right (monotone_cdf μ hxr)]
    · have hrx : r ≤ x := (not_le.mp hxr).le
      have hinter : Ioc l r ∩ Iic x = Ioc l r :=
        inter_eq_left.mpr fun _ hy ↦ hy.2.trans hrx
      rw [hinter, measureReal_Ioc_eq_cdf_sub μ hlr.le,
        max_eq_right (monotone_cdf μ hlx), min_eq_left (monotone_cdf μ hrx),
        div_self (sub_ne_zero.mpr hLR.ne')]

/-- For `0 < u < 1`, the `u`-quantile of `μ` conditioned on `(l, r]` is the quantile of `μ`
at the affinely rescaled cdf level `cdf μ l + u * (cdf μ r - cdf μ l)`. -/
theorem quantile_cond_Ioc {l r u : ℝ} (hLR : cdf μ l < cdf μ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ioc l r)).quantile u =
      μ.quantile (cdf μ l + u * (cdf μ r - cdf μ l)) := by
  have hD : 0 < cdf μ r - cdf μ l := sub_pos.mpr hLR
  have hqL : cdf μ l < cdf μ l + u * (cdf μ r - cdf μ l) := by
    nlinarith [mul_pos hu.1 hD]
  have hqR : cdf μ l + u * (cdf μ r - cdf μ l) < cdf μ r := by
    nlinarith [hu.2]
  -- The clipped-cdf formula turns its quantile adjunction into the adjunction for `μ` at the
  -- rescaled level. Splitting at the two clipping thresholds avoids any atomlessness assumption.
  have hlevel (x : ℝ) :
      u ≤ cdf (ProbabilityTheory.cond μ (Ioc l r)) x ↔
        cdf μ l + u * (cdf μ r - cdf μ l) ≤ cdf μ x := by
    rw [cdf_cond_Ioc μ hLR]
    by_cases hxL : cdf μ x ≤ cdf μ l
    · rw [max_eq_left hxL, min_eq_right hLR.le, sub_self, zero_div]
      constructor <;> intro h <;> linarith [hu.1, hqL]
    · have hLx : cdf μ l ≤ cdf μ x := (not_le.mp hxL).le
      by_cases hRx : cdf μ r ≤ cdf μ x
      · rw [max_eq_right hLx, min_eq_left hRx, div_self hD.ne']
        constructor
        · intro _
          exact hqR.le.trans hRx
        · intro _
          exact hu.2.le
      · have hxR : cdf μ x ≤ cdf μ r := (not_le.mp hRx).le
        rw [max_eq_right hLx, min_eq_right hxR, le_div_iff₀ hD]
        constructor <;> intro h <;> linarith
  exact quantile_eq_of_le_cdf_iff _ _ hlevel

end MeasureTheory.Measure
