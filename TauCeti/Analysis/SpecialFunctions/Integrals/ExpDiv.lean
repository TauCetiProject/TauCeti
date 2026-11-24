/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential-integral tail integrability

This file establishes tail integrability of the exponential-integral kernel `exp u / u` on
intervals bounded away from `0`, without depending on Gamma differentiation or `TauCeti.Real.li`:

* `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for `a > 0`.
* By reflection, `u ↦ exp u / u` is integrable on `(-∞, y]` for `y < 0`.

## Main results

* `Real.integrableOn_exp_neg_div_Ioi`: `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for `a > 0`.
* `Real.integrableOn_exp_div_Iic`: `u ↦ exp u / u` is integrable on `(-∞, y]` for `y < 0`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2.
-/

public section

open MeasureTheory Set

namespace Real

/-- `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for every `a > 0`. -/
theorem integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ exp (-t) / t) (Ioi a) := by
  refine Integrable.mono' (g := fun t : ℝ ↦ exp (-t) / a)
    ((integrableOn_exp_neg_Ioi a).div_const a)
    ((continuous_exp.comp continuous_neg).measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : a < t)
  rw [norm_eq_abs, abs_div, abs_of_pos (exp_pos _), abs_of_pos (ha.trans ht)]
  exact div_le_div_of_nonneg_left (exp_pos _).le ha ht.le

/-- `u ↦ exp u / u` is integrable on `(-∞, y]` whenever `y < 0`. -/
theorem integrableOn_exp_div_Iic {y : ℝ} (hy : y < 0) :
    IntegrableOn (fun u : ℝ ↦ exp u / u) (Iic y) := by
  have hcomp := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
    (Homeomorph.neg ℝ).measurableEmbedding).mpr (integrableOn_exp_neg_div_Ioi (neg_pos.mpr hy))
  have hIio : IntegrableOn (fun u : ℝ ↦ exp u / u) (Iio y) := by
    simpa [Function.comp_def, div_neg] using hcomp.neg
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact hIio

end Real
