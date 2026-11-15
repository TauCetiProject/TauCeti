/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Pointwise bounds for the real-valued `Lᵖ` norm

A pointwise bound `‖f x‖ ≤ c ‖g x‖` almost everywhere bounds the real-valued `Lᵖ` norm:
`lpNorm f p μ ≤ c * lpNorm g p μ` (`MeasureTheory.lpNorm_le_mul_lpNorm_of_ae_le_mul`). This is
the `lpNorm` form of Mathlib's `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`. Since
`lpNorm` is `0` off `Lᵖ`, the hypothesis `g ∈ Lᵖ(μ)` is needed. It is the estimate for
multiplication by a bounded measurable coefficient, as for the lower-order terms of a
differential operator.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α F G : Type*} {m : MeasurableSpace α} [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p : ℝ≥0∞} {μ : Measure α}

/-- **A pointwise bound bounds `lpNorm`.** If `g ∈ Lᵖ(μ)` and `‖f x‖ ≤ c ‖g x‖` for almost every
`x`, then `lpNorm f p μ ≤ c * lpNorm g p μ`. -/
theorem lpNorm_le_mul_lpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : MemLp g p μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
    lpNorm f p μ ≤ c * lpNorm g p μ := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0` the bound forces `f = 0` and `g = 0` almost everywhere.
    obtain ⟨hf0, hg0⟩ := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    rw [← toReal_eLpNorm, ← toReal_eLpNorm, hf0, hg0, ENNReal.toReal_zero, mul_zero]
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, ← ENNReal.toReal_ofReal hc, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf h p)

end MeasureTheory
