/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Elementary inequalities in seminormed rings

This file records elementary consequences of the submultiplicativity of the norm.
-/

public section

namespace TauCeti

/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one {K : Type*} [NonUnitalSeminormedRing K] (u v : K) (hu : ‖u‖ < 1)
    (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

end TauCeti

end
