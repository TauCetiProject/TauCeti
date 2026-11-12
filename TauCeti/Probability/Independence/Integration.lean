/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Independence.Integration

/-!
# Square integrability of independent products

The product of two independent square-integrable real random variables is square integrable.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.IndepFun

/-- The product of independent square-integrable real random variables is square integrable. -/
theorem memLp_two_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    MemLp (X * Y) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2 ?_
  simpa only [Pi.mul_def, mul_pow, Function.comp_def, id_eq] using
    (h.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
      hX.integrable_sq hY.integrable_sq

end ProbabilityTheory.IndepFun
