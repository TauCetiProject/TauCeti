/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The critical points of `cos (2 (θ - ρ))`

The critical points of `θ ↦ cos (2 (θ - ρ))` are spaced `π / 2` apart, and maxima and minima
alternate: the neighbours `m ± π / 2` of a critical point `m` are of the opposite kind,
`cos (2 (m ± π / 2 - ρ)) = -cos (2 (m - ρ))`. So an angle within `π / 2` of a critical point `m`
is either `m` itself or within `π / 2` of a critical point of the opposite kind
(`Real.eq_of_forall_cos_eq_neg_not_abs_sub_lt`).
-/

public section

open Set

namespace Real

/-- An angle `θ` within `π / 2` of a critical point `m` of `cos (2 (θ - ρ))` is `m` itself, if it
is not within `π / 2` of any critical point `m'` of the opposite kind. -/
theorem eq_of_forall_cos_eq_neg_not_abs_sub_lt {θ m ρ : ℝ}
    (hθ : θ ∈ Ioo (m - π / 2) (m + π / 2))
    (h : ∀ m', cos (2 * (m' - ρ)) = -cos (2 * (m - ρ)) → ¬ |θ - m'| < π / 2) : θ = m := by
  rcases lt_trichotomy θ m with hlt | heq | hgt
  · have hsub : 2 * (m - π / 2 - ρ) = 2 * (m - ρ) - π := by ring
    refine (h (m - π / 2) ?_ ?_).elim
    · rw [hsub, cos_sub_pi]
    · rw [abs_lt]; constructor <;> linarith [hθ.1]
  · exact heq
  · have hadd : 2 * (m + π / 2 - ρ) = 2 * (m - ρ) + π := by ring
    refine (h (m + π / 2) ?_ ?_).elim
    · rw [hadd, cos_add_pi]
    · rw [abs_lt]; constructor <;> linarith [hθ.2]

end Real
