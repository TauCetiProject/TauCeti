/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation

/-!
# Metric variation of a continuously differentiable curve

For a continuously differentiable curve in a real normed space, its
metric total variation equals the integral of the norm of its derivative.

The metric derivative identity for absolutely continuous curves, together with identification
of the derivative at interior points, gives the equality.

## Main result

* `TauCeti.eVariationOn_eq_lintegral_enorm_derivWithin`: metric variation
  equals the integral of the derivative norm.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The metric total variation of a `C¹` curve in a real normed space equals the integral
of the norm of its derivative. Completeness of the target is not needed. -/
theorem eVariationOn_eq_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty hab]
    simp
  have hf' : ContDiffOn ℝ 1 f (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hf
  have hAC := hf'.absolutelyContinuousOnInterval
  rw [← uIcc_of_le hab, hAC.eVariationOn_eq_lintegral_metricDerivative,
    uIoc_of_le hab, restrict_Ioc_eq_restrict_Icc, uIcc_of_le hab]
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hd : DifferentiableAt ℝ f t :=
    (hf t (Ioo_subset_Icc_self ht)).contDiffAt (Icc_mem_nhds ht.1 ht.2)
      |>.differentiableAt one_ne_zero
  rw [hd.hasDerivAt.metricDerivative_eq,
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

end

end TauCeti
