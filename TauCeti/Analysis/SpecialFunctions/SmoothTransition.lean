/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Derivative of the smooth transition function

Mathlib's `Analysis/SpecialFunctions/SmoothTransition.lean` proves that
`Real.smoothTransition` is smooth and equals one on `[1, ∞)`, but states no derivative values.
This file records that its derivative vanishes on the open rays `(-∞, 0)` and `(1, ∞)`, where the
function is locally constant, so that the derivative is compactly supported. Being continuous, it
is then bounded, which bounds the gradients of cutoffs built from `Real.smoothTransition`.

## Main declarations

* `Real.smoothTransition.deriv_of_neg`: `deriv Real.smoothTransition x = 0` for `x < 0`.
* `Real.smoothTransition.deriv_of_one_lt`: `deriv Real.smoothTransition x = 0` for `1 < x`.
* `Real.smoothTransition.hasCompactSupport_deriv`: the derivative is compactly supported.
-/

public section

open Filter Set
open scoped Topology

namespace Real.smoothTransition

/-- The smooth transition function has derivative zero to the left of `0`, where it is
identically zero. -/
theorem deriv_of_neg {x : ℝ} (hx : x < 0) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hx) fun _ ht => zero_of_nonpos (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The smooth transition function has derivative zero to the right of `1`, where it is
identically one. -/
theorem deriv_of_one_lt {x : ℝ} (hx : 1 < x) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
    eventually_of_mem (Ioi_mem_nhds hx) fun _ ht => one_of_one_le (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition function is supported in `[0, 1]`. -/
theorem hasCompactSupport_deriv : HasCompactSupport (deriv smoothTransition) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    rcases not_and_or.1 hx with h | h
    · exact deriv_of_neg (not_le.1 h)
    · exact deriv_of_one_lt (not_le.1 h)

end Real.smoothTransition
