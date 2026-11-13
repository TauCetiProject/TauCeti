/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Truncated second moments

For a real square-integrable function `X` and a level `ε`, the truncated square
`X ^ 2 𝟙{ε ≤ |X|}` is integrable (`MeasureTheory.MemLp.integrable_indicator_sq`), and on a
probability space the second moment splits as `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`
(`MeasureTheory.MemLp.integral_sq_le_sq_add_integral_indicator`). The truncated second moment is
the quantity in the Lindeberg condition of the central limit theorem, and the split is how that
condition controls each individual variance. Only almost-everywhere measurability is used, through
`Integrable.indicator₀`.
-/

public section

open Set

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- The truncated square `X ^ 2 𝟙{ε ≤ |X|}` of a square-integrable function is integrable. -/
theorem MemLp.integrable_indicator_sq (hX : MemLp X 2 P) (ε : ℝ) :
    Integrable ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) P :=
  hX.integrable_sq.indicator₀
    (nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hX.aestronglyMeasurable.aemeasurable))

/-- Splitting the second moment at level `ε`: `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`. -/
theorem MemLp.integral_sq_le_sq_add_integral_indicator [IsProbabilityMeasure P]
    (hX : MemLp X 2 P) (ε : ℝ) :
    ∫ ω, X ω ^ 2 ∂P ≤ ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
  have h := hX.integrable_indicator_sq ε
  calc ∫ ω, X ω ^ 2 ∂P
      ≤ ∫ ω, (ε ^ 2 + ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω) ∂P := by
        refine integral_mono hX.integrable_sq ((integrable_const _).add h) fun ω ↦ ?_
        by_cases hω : ε ≤ |X ω|
        · rw [indicator_of_mem (s := {ω | ε ≤ |X ω|}) hω]
          linarith [sq_nonneg ε]
        · rw [indicator_of_notMem (s := {ω | ε ≤ |X ω|}) hω, add_zero,
            ← sq_abs (X ω)]
          have := abs_nonneg (X ω)
          nlinarith [not_le.mp hω]
    _ = ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
        rw [integral_add (integrable_const _) h]
        simp

end MeasureTheory
