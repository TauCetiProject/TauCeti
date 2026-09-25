/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Cumulative distribution functions

This file records basic properties of cumulative distribution functions. In particular, the cdf
of an atomless real probability measure is continuous.

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `MeasureTheory.Measure.continuous_cdf_of_noAtoms` proves continuity for atomless real laws;
* `MeasureTheory.Measure.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `MeasureTheory.Measure.cdf_map_natCast_of_neg` evaluates it below the origin.
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- At a nonnegative point, the cdf of a natural-valued law cast to the reals is the cumulative
mass of the initial segment below the natural floor of that point. -/
theorem cdf_map_natCast {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = μ.real (Iic ⌊x⌋₊) := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
    ext k
    simp only [mem_preimage, mem_Iic]
    exact (Nat.le_floor_iff hx).symm
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]

/-- Below the origin, the cdf of a natural-valued law cast to the reals vanishes: the law is
carried by the natural numbers. -/
theorem cdf_map_natCast_of_neg {x : ℝ} (hx : x < 0) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
    ext k
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_empty]

/-- **CDF continuity from null singletons.** The cumulative distribution function of a
probability measure on `ℝ` is continuous when every singleton has measure zero. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
    intro x
    have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hsing
    have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
    have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
    exact le_antisymm hle (by linarith)
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
    ((cdf ν).right_continuous x).rightLim_eq]

end MeasureTheory.Measure
