/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sine at a natural fraction of pi

The sine of `π / k` is positive for natural `k ≥ 2`.
-/

public section

namespace TauCeti

/-- For a natural denominator at least two, the sine of `π / k` is positive. -/
theorem sin_pi_div_pos {k : ℕ} (hk : 2 ≤ k) : 0 < Real.sin (Real.pi / k) := by
  have hk₁ : (1 : ℝ) < k := by exact_mod_cast hk
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self Real.pi_pos hk₁)

end TauCeti
