/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable.Exit

/-!
# Exit points on the unit circle: checks

Checks for `TauCeti.ConvexTable.exitParam` on the unit circle `s ↦ exp(is)`, the convex table
`TauCeti.ConvexTable.circle 1` of perimeter `2π`: leaving `γ(0) = 1` at the angle `π/2` the ball
exits at the antipodal point `s₁ = π`, and at the angle `π/3` it exits at `s₁ = 2π/3`.
-/

public section

noncomputable section

open Set TauCeti ConvexTable

namespace TauCeti.Examples.ConvexTableExit

/-- The unit circle has positive perimeter `2π`. -/
instance instFactPosTwoPiMulOne : Fact (0 < 2 * Real.pi * 1) := ⟨by positivity⟩

/-- On the unit circle the chord leaving `γ(0)` at the angle `π/2` exits at the antipodal point
`s₁ = π`. -/
example : (circle 1).exitParam 0 (Real.pi / 2) = Real.pi := by
  rw [exitParam_circle 1 0 ⟨by positivity, by linarith [Real.pi_pos]⟩]
  ring

/-- On the unit circle the chord leaving `γ(0)` at the angle `π/3` exits at `s₁ = 2π/3`. -/
example : (circle 1).exitParam 0 (Real.pi / 3) = 2 * Real.pi / 3 := by
  rw [exitParam_circle 1 0 ⟨by positivity, by linarith [Real.pi_pos]⟩]
  ring

end TauCeti.Examples.ConvexTableExit
