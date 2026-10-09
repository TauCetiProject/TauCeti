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
This file records that its derivative vanishes on the open ray `(1, ∞)`, where the function is
locally constant.

## Main declarations

* `Real.smoothTransition.deriv_of_one_lt`: `deriv Real.smoothTransition x = 0` for `1 < x`.
-/

public section

open Filter Set
open scoped Topology

namespace Real.smoothTransition

/-- The smooth transition function has derivative zero to the right of `1`, where it is
identically one. -/
theorem deriv_of_one_lt {x : ℝ} (hx : 1 < x) : deriv smoothTransition x = 0 := by
  have h : smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
    eventually_of_mem (Ioi_mem_nhds hx) fun _ ht => one_of_one_le (le_of_lt ht)
  rw [h.deriv_eq, deriv_const]

end Real.smoothTransition
