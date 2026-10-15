/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Section.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Quadratic sections are balls

For `u(y) = ‖y‖² / 2` and the supporting slope `ℓ(y) = ⟪x, y⟫`, the section at `x`
of height `h` is exactly `ball x (√(2h))`. The identity includes nonpositive heights:
both sides are empty. It verifies the strict boundary and the factor of two in the
section convention. No finite-dimensionality or completeness assumption is needed.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Birkhäuser, 2016, §1.8.
-/

public section

open Set InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sections of the half squared norm with its supporting slope are precisely balls.
The formula also holds for zero and negative heights, when the section is empty. -/
theorem convexSection_norm_sq_div_two (x : E) (h : ℝ) :
    convexSection univ (fun y : E ↦ ‖y‖ ^ 2 / 2) x (innerₗ E x) h =
      Metric.ball x (Real.sqrt (2 * h)) := by
  ext y
  simp only [mem_convexSection_iff, mem_univ, true_and, innerₗ_apply_apply,
    inner_sub_right, Metric.mem_ball, dist_eq_norm]
  rw [Real.lt_sqrt (norm_nonneg _)]
  have hnorm := norm_sub_sq_real y x
  rw [real_inner_comm] at hnorm
  have hself := real_inner_self_eq_norm_sq x
  constructor <;> intro hy <;> nlinarith

end TauCeti
