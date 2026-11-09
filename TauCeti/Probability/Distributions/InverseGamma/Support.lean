/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Basic
public import Mathlib.MeasureTheory.Measure.Support

import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of inverse-gamma laws

For positive shape and scale, the inverse-gamma density is nonzero exactly on the positive
half-line, whereas the measure has topological support `[0, ∞)`. In particular, zero belongs to
the topological support even though the law is almost surely strictly positive. Invalid
parameters give the zero density and measure, both with empty support.

These characterizations distinguish density positivity, almost-sure positivity, and topological
support for the inverse-gamma law defined in `InverseGamma.Basic`.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The inverse-gamma density is nonzero exactly at positive points when its shape and scale
are positive, and vanishes everywhere otherwise. -/
@[simp]
theorem support_inverseGammaPDF (a r : ℝ) :
    Function.support (inverseGammaPDF a r) = if 0 < a ∧ 0 < r then Ioi 0 else ∅ := by
  by_cases h : 0 < a ∧ 0 < r
  · rw [ite_eq_left h]
    ext x
    rw [Function.mem_support, mem_Ioi]
    constructor
    · intro hx
      by_contra hxpos
      exact hx (inverseGammaPDF_of_nonpos (not_lt.mp hxpos) a r)
    · intro hx
      rw [inverseGammaPDF_of_pos h.1 h.2 hx, ENNReal.ofReal_ne_zero_iff]
      exact mul_pos
        (mul_pos (div_pos (Real.rpow_pos_of_pos h.2 _) (Real.Gamma_pos_of_pos h.1))
          (Real.rpow_pos_of_pos hx _)) (Real.exp_pos _)
  · ext x
    simp [h, Function.mem_support]

/-- A valid inverse-gamma law has topological support `[0, ∞)`. At invalid parameters its
topological support is empty. -/
@[simp]
theorem support_inverseGammaMeasure (a r : ℝ) :
    (inverseGammaMeasure a r).support = if 0 < a ∧ 0 < r then Ici 0 else ∅ := by
  by_cases h : 0 < a ∧ 0 < r
  · rw [ite_eq_left h, inverseGammaMeasure_eq_withDensity,
      Measure.support_withDensity_eq_closure (measurable_inverseGammaPDF a r) isOpen_Ioi
        (by simpa only [ite_eq_left h] using support_inverseGammaPDF a r), closure_Ioi]
  · simp [h]

end TauCeti.Probability
