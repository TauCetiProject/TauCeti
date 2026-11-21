/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Basic linear-bound helpers for Chebyshev's `θ` and `ψ`

This file records elementary consequences of linear upper bounds `θ y ≤ c * y` and
`ψ y ≤ c * y` on `[2, ∞)` for Mathlib's Chebyshev functions `Chebyshev.theta` and `Chebyshev.psi`.
Since `0 < θ 2 ≤ ψ 2`, any such bound forces `0 < c`, and since both `θ` and `ψ` vanish below
`2`, the linear bound extends automatically from `[2, ∞)` to `[0, ∞)`.

## Main results

* `TauCeti.pos_of_theta_le`, `TauCeti.pos_of_psi_le`: positivity of `c` from a linear upper
  bound on `θ` or `ψ` on `[2, ∞)`.
* `TauCeti.theta_le_mul_of_two_le`, `TauCeti.psi_le_mul_of_two_le`: extension of a linear upper
  bound on `θ` or `ψ` from `[2, ∞)` to `[0, ∞)`.
-/

public section

open scoped Chebyshev

namespace TauCeti

/-- Any linear upper bound `θ y ≤ c * y` on `[2, ∞)` forces `0 < c`. -/
theorem pos_of_theta_le {c : ℝ} (hθ : ∀ y, 2 ≤ y → θ y ≤ c * y) : 0 < c :=
  pos_of_mul_pos_left ((Chebyshev.theta_pos le_rfl).trans_le (hθ 2 le_rfl)) zero_le_two

/-- Any linear upper bound `ψ y ≤ c * y` on `[2, ∞)` forces `0 < c`. -/
theorem pos_of_psi_le {c : ℝ} (hψ : ∀ y, 2 ≤ y → ψ y ≤ c * y) : 0 < c :=
  pos_of_theta_le fun y hy ↦ (Chebyshev.theta_le_psi y).trans (hψ y hy)

/-- Extending a linear upper bound `θ t ≤ c * t` from `[2, ∞)` to `[0, ∞)`. -/
theorem theta_le_mul_of_two_le {c y : ℝ} (hy : 0 ≤ y)
    (hθ : ∀ t, 2 ≤ t → θ t ≤ c * t) : θ y ≤ c * y := by
  rcases lt_or_ge y 2 with hy2 | hy2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hy2]
    exact mul_nonneg (pos_of_theta_le hθ).le hy
  · exact hθ y hy2

/-- Extending a linear upper bound `ψ t ≤ c * t` from `[2, ∞)` to `[0, ∞)`. -/
theorem psi_le_mul_of_two_le {c y : ℝ} (hy : 0 ≤ y) (hψ : ∀ t, 2 ≤ t → ψ t ≤ c * t) :
    ψ y ≤ c * y := by
  rcases lt_or_ge y 2 with hy2 | hy2
  · rw [Chebyshev.psi_eq_zero_of_lt_two hy2]
    exact mul_nonneg (pos_of_psi_le hψ).le hy
  · exact hψ y hy2

end TauCeti
