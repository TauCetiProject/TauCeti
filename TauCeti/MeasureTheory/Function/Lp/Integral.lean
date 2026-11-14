/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals of pointwise expressions in `Lᵖ` classes

The representative of `-g` for an `Lᵖ` class `g` agrees with `-g x` only almost everywhere
(`MeasureTheory.Lp.coeFn_neg`), so integrals of expressions in `(-g) x` do not simplify
pointwise. This file records the resulting integral identity
`∫ (-g) x * h x ∂μ = -∫ g x * h x ∂μ` (`MeasureTheory.Lp.integral_neg_mul`), which applies to set
integrals by taking `μ` to be a restricted measure.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedRing E] [NormedSpace ℝ E]
  {p : ℝ≥0∞}

/-- Negating an `Lᵖ` class negates its integral against any function `h`. -/
theorem integral_neg_mul (g : Lp E p μ) (h : α → E) :
    ∫ x, (-g) x * h x ∂μ = -∫ x, g x * h x ∂μ := by
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg g] with x hx
  rw [hx, Pi.neg_apply, neg_mul]

end MeasureTheory.Lp
