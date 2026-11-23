/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith

/-!
# Comparing coefficients of diverging affine weights

A frequently valid comparison with a common parameter tending to negative infinity compares
the two coefficients. The argument uses only ordered-field algebra and the order filter.

## References

The ancient-origin argument in the formalization references
https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Filter

namespace TauCeti

/-- A frequently valid comparison with common diverging linear weights compares the coefficients.
No topology on the ordered field is required. -/
theorem le_of_frequently_mul_sub_le {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {a b A B : 𝕜}
    (hfinite : ∃ᶠ T : 𝕜 in atBot, A * (a - T) ≤ B * (b - T)) : A ≤ B := by
  by_contra! hAB
  have hpos : 0 < A - B := sub_pos.mpr hAB
  have hlarge : ∀ᶠ T : 𝕜 in atBot, B * (b - T) < A * (a - T) := by
    filter_upwards [eventually_lt_atBot ((A * a - B * b) / (A - B))] with T hT
    have := (lt_div_iff₀ hpos).mp hT
    nlinarith
  obtain ⟨T, hle, hlt⟩ := (hfinite.and_eventually hlarge).exists
  exact (not_lt_of_ge hle) hlt


end TauCeti
