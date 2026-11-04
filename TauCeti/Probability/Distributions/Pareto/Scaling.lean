/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Pareto.Basic
public import Mathlib.Probability.HasLaw
import TauCeti.Probability.Distributions.Affine

/-!
# Positive scaling of Pareto laws

Multiplication by a positive constant multiplies the threshold of a Pareto law and preserves
its shape. The measure identity and its random-variable form allow a change of scale without
recomputing the density or the cumulative distribution function.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  Chapter 20.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Scaling a Pareto law by a positive constant multiplies its threshold and leaves its shape
unchanged. -/
@[simp]
theorem paretoMeasure_map_const_mul {t r b : ℝ} (ht : 0 < t) (hr : 0 < r) (hb : 0 < b) :
    (paretoMeasure t r).map (b * ·) = paretoMeasure (b * t) r := by
  let _ := isProbabilityMeasure_paretoMeasure ht hr
  let _ := isProbabilityMeasure_paretoMeasure (mul_pos hb ht) hr
  apply Measure.eq_of_cdf
  ext x
  have hmap : (b * ·) = (fun y : ℝ => 0 + b * y) := by simp
  rw [hmap, cdf_map_affine_of_pos hb, sub_zero, cdf_paretoMeasure_eq ht hr,
    cdf_paretoMeasure_eq (mul_pos hb ht) hr]
  simp [div_lt_iff₀ hb, div_div_eq_mul_div, mul_comm]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- Multiplying a Pareto variable by a positive constant multiplies its threshold and preserves
its shape. -/
theorem const_mul_paretoMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {t r b : ℝ} (hX : HasLaw X (paretoMeasure t r) P)
    (ht : 0 < t) (hr : 0 < r) (hb : 0 < b) :
    HasLaw (fun ω => b * X ω) (paretoMeasure (b * t) r) P := by
  rw [← TauCeti.Probability.paretoMeasure_map_const_mul ht hr hb]
  exact (hasLaw_map (measurable_const_mul b).aemeasurable).fun_comp hX

end ProbabilityTheory.HasLaw
