/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Elementary interval integrals

Interval integrals of elementary functions in closed form, continuing Mathlib's
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`.

## Main declarations

* `TauCeti.integral_one_div_sqrt_one_sub_sq`: `∫ x in a..b, 1 / √(1 - x²) = arcsin b - arcsin a`
  for `-1 < a ≤ b < 1`.
-/

public section

namespace TauCeti

/-- The integral of `1 / √(1 - x²)` is `arcsin`. -/
theorem integral_one_div_sqrt_one_sub_sq {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ x in a..b, 1 / Real.sqrt (1 - x ^ 2) = Real.arcsin b - Real.arcsin a := by
  have hIcc : Set.uIcc a b ⊆ Set.Ioo (-1) 1 := by
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Ioo ha hb
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ ?_) ?_
  · exact Real.hasDerivAt_arcsin (hIcc hx).1.ne' (hIcc hx).2.ne
  · refine ContinuousOn.intervalIntegrable (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    · intro x hx
      have hx' := hIcc hx
      exact (Real.sqrt_pos.2 (by nlinarith [hx'.1, hx'.2])).ne'

end TauCeti
