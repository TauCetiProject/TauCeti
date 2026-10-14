/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Trigonometric functions on the unit interval

The cosine `t ↦ cos (π t)` is injective on the unit interval `I`, and the sine `t ↦ sin (π t)` is
positive on its interior.

## Main declarations

* `TauCeti.cos_pi_mul_injOn`: `t ↦ cos (π t)` is injective on `I`.
* `TauCeti.sin_pi_mul_pos`: `sin (π t) > 0` for `t ∈ I` different from `0` and `1`.
-/

public section

open Real
open scoped unitInterval

namespace TauCeti

/-- `t ↦ cos (π t)` is injective on the unit interval. -/
theorem cos_pi_mul_injOn : Set.InjOn (fun t : I => cos (π * t)) Set.univ := by
  intro a _ b _ h
  refine Subtype.ext (mul_left_cancel₀ pi_ne_zero (Real.injOn_cos ?_ ?_ h))
  · exact ⟨by positivity [a.2.1], mul_le_of_le_one_right pi_pos.le a.2.2⟩
  · exact ⟨by positivity [b.2.1], mul_le_of_le_one_right pi_pos.le b.2.2⟩

/-- `sin (π t)` is positive on the open unit interval. -/
theorem sin_pi_mul_pos {t : I} (h0 : t ≠ 0) (h1 : t ≠ 1) : 0 < sin (π * t) := by
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
  exact sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])

end TauCeti
