/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Circle

/-!
# The invariant graphs of the circular table: checks

Checks for `TauCeti.StrictConvexBilliardTable.isInvariantGraph_circle_iff` and
`TauCeti.StrictConvexBilliardTable.circleRotationNumberHomeomorph`.

* A perturbed level `v = c + ε sin (s / R)` with `ε ≠ 0` is not an invariant graph of the
  circular table of radius `R`, since it is not constant.
* The rotation number of the level `v = 0` is `1/2`, and the level with rotation number `1/3` is
  `v = cos (π / 3) = 1/2`.
-/

public section

noncomputable section

open Real Set TauCeti StrictConvexBilliardTable

namespace TauCeti.Examples.CircleInvariantGraph

attribute [local instance] Complex.finrank_real_complex_fact

variable {R : ℝ} (hR : 0 < R)

/-- A perturbed level `v = c + ε sin (s / R)`, `ε ≠ 0`, is not an invariant graph of the circular
table. -/
theorem not_isInvariantGraph_circle_add_sin {c ε : ℝ} (hε : ε ≠ 0) :
    ¬ (circle hR).IsInvariantGraph fun s ↦ c + ε * sin (s / R) := by
  intro h
  obtain ⟨d, -, hd⟩ := (isInvariantGraph_circle_iff hR).1 h
  have h₀ := congrFun hd 0
  have h₁ := congrFun hd (π / 2 * R)
  simp only [zero_div, sin_zero, mul_zero, add_zero] at h₀
  rw [mul_div_cancel_right₀ _ hR.ne', sin_pi_div_two, mul_one] at h₁
  exact hε (by linarith)

/-- The level `v = 0` has rotation number `1/2`. -/
theorem circleRotationNumberHomeomorph_zero :
    (circleRotationNumberHomeomorph ⟨0, by norm_num, by norm_num⟩ : ℝ) = 1 / 2 := by
  rw [coe_circleRotationNumberHomeomorph_apply, arccos_zero]
  field_simp

/-- The level with rotation number `1/3` is `v = cos (π / 3) = 1/2`. -/
theorem circleRotationNumberHomeomorph_symm_one_third :
    (circleRotationNumberHomeomorph.symm ⟨1 / 3, by norm_num, by norm_num⟩ : ℝ) = 1 / 2 := by
  rw [coe_circleRotationNumberHomeomorph_symm_apply, show π * (1 / 3) = π / 3 by ring,
    cos_pi_div_three]

end TauCeti.Examples.CircleInvariantGraph
