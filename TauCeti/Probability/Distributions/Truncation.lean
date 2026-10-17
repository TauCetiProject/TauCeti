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

* `MeasureTheory.Measure.cdf_cond_Ioc` — the cdf of a law conditioned on `(l, r]`;
* `MeasureTheory.Measure.quantile_cond_Ioc` — the corresponding interior quantile formula.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The cdf of `μ` conditioned on `(l, r]` is the increment of the original cdf above `cdf μ l`,
clipped between the endpoint masses and normalized by `cdf μ r - cdf μ l`. -/
theorem cdf_cond_Ioc {l r : ℝ} (hLR : cdf μ l < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioc l r)) x =
      (min (cdf μ r) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (cdf μ r - cdf μ l) := by
  have hlr : l < r := by
    by_contra h
    exact (not_lt_of_ge (monotone_cdf μ (not_lt.mp h))) hLR
  have hmassReal : 0 < μ.real (Ioc l r) := by
    rw [measureReal_Ioc_eq_cdf_sub μ hlr.le]
    exact sub_pos.mpr hLR
  have hmass : μ (Ioc l r) ≠ 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ _)).not.mp hmassReal.ne'
  let _ := ProbabilityTheory.cond_isProbabilityMeasure hmass
  rw [cdf_eq_real, measureReal_def, ProbabilityTheory.cond_apply measurableSet_Ioc,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_inv_mul, ← measureReal_def,
    ← measureReal_def, measureReal_Ioc_eq_cdf_sub μ hlr.le]
  by_cases hxl : x ≤ l
  · have hinter : Ioc l r ∩ Iic x = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_empty_iff_false, iff_false]
      rintro ⟨⟨hly, _⟩, hyx⟩
      exact (not_lt_of_ge (hyx.trans hxl)) hly
    rw [hinter, measureReal_empty]
    have hFxL : cdf μ x ≤ cdf μ l := monotone_cdf μ hxl
    rw [max_eq_left hFxL, min_eq_right hLR.le, sub_self, zero_div]
  · have hlx : l ≤ x := (not_le.mp hxl).le
    by_cases hxr : x ≤ r
    · have hinter : Ioc l r ∩ Iic x = Ioc l x := by
        ext y
        simp only [mem_inter_iff, mem_Ioc, mem_Iic]
        constructor
        · rintro ⟨⟨hly, _⟩, hyx⟩
          exact ⟨hly, hyx⟩
        · rintro ⟨hly, hyx⟩
          exact ⟨⟨hly, hyx.trans hxr⟩, hyx⟩
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
  have hlr : l < r := by
    by_contra h
    exact (not_lt_of_ge (monotone_cdf μ (not_lt.mp h))) hLR
  have hmassReal : 0 < μ.real (Ioc l r) := by
    rw [measureReal_Ioc_eq_cdf_sub μ hlr.le]
    exact sub_pos.mpr hLR
  have hmass : μ (Ioc l r) ≠ 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ _)).not.mp hmassReal.ne'
  let _ := ProbabilityTheory.cond_isProbabilityMeasure hmass
  have hD : 0 < cdf μ r - cdf μ l := sub_pos.mpr hLR
  have hqL : cdf μ l < cdf μ l + u * (cdf μ r - cdf μ l) := by
    nlinarith [mul_pos hu.1 hD]
  have hq0 : 0 < cdf μ l + u * (cdf μ r - cdf μ l) := by
    nlinarith [cdf_nonneg μ l]
  have hqR : cdf μ l + u * (cdf μ r - cdf μ l) < cdf μ r := by
    nlinarith [hu.2]
  have hq1 : cdf μ l + u * (cdf μ r - cdf μ l) < 1 :=
    hqR.trans_le (cdf_le_one μ r)
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
  apply le_antisymm
  · rw [quantile_le_iff _ hu.1 hu.2]
    exact (hlevel _).mpr (le_cdf_quantile μ hq1)
  · rw [quantile_le_iff _ hq0 hq1]
    exact (hlevel _).mp
      (le_cdf_quantile (ProbabilityTheory.cond μ (Ioc l r)) hu.2)

end MeasureTheory.Measure
