/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lebesgue integrals of suprema of real families

For real families `X i` and `Y i` with `X i ≤ C Y i` pointwise on the indices satisfying `p`, with
`C ≥ 0`, a finite Lebesgue integral of `sup_{p i} (Y i)⁺` gives a finite Lebesgue integral of
`sup_{p i} (X i)⁺`. With `p i = (i ≤ T)` this transfers integrability of a running maximum along a
pointwise domination, as for a process dominated by a constant multiple of a martingale.

## Main declarations

* `MeasureTheory.lintegral_iSup_ofReal_lt_top_of_le_mul`: domination of finite Lebesgue integrals
  of suprema.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- If `X i ≤ C Y i` for all indices `i` with `p i`, and `C ≥ 0`, then the Lebesgue integral of
`sup_{p i} ENNReal.ofReal (X i)` is finite whenever that of `sup_{p i} ENNReal.ofReal (Y i)` is. -/
theorem lintegral_iSup_ofReal_lt_top_of_le_mul {p : ι → Prop} {X Y : ι → α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hXY : ∀ x i, p i → X i x ≤ C * Y i x)
    (hY : ∫⁻ x, ⨆ (i) (_ : p i), ENNReal.ofReal (Y i x) ∂μ < ∞) :
    ∫⁻ x, ⨆ (i) (_ : p i), ENNReal.ofReal (X i x) ∂μ < ∞ := by
  calc ∫⁻ x, ⨆ (i) (_ : p i), ENNReal.ofReal (X i x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal C * ⨆ (i) (_ : p i), ENNReal.ofReal (Y i x) ∂μ := by
        refine lintegral_mono fun x ↦ iSup₂_le fun i hi ↦ ?_
        refine (ENNReal.ofReal_le_ofReal (hXY x i hi)).trans ?_
        rw [ENNReal.ofReal_mul hC]
        exact mul_le_mul_right (le_iSup₂ (f := fun i _ ↦ ENNReal.ofReal (Y i x)) i hi) _
    _ = ENNReal.ofReal C * ∫⁻ x, ⨆ (i) (_ : p i), ENNReal.ofReal (Y i x) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hY

end MeasureTheory
