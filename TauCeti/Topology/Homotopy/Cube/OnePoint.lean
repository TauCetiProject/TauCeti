/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Compactification.OnePoint.UnitBall
public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Collapsing the boundary of the cube

The cube `I^N` with its boundary `Cube.boundary N` collapsed to a point is the one-point
compactification of `N → ℝ`: the cube is the closed unit ball of the sup norm
(`TauCeti.cubeHomeomorphClosedBall`), and the closed unit ball with its boundary sphere collapsed
is `OnePoint (N → ℝ)` (`TauCeti.unitBallToOnePoint`). Together with the homeomorphism of
`OnePoint (N → ℝ)` with a sphere, this realizes the sphere `S^n` as the quotient `I^n / ∂I^n`.

## Main declarations

* `TauCeti.cubeToOnePoint`: the continuous collapse `I^N → OnePoint (N → ℝ)`.
* `TauCeti.cubeToOnePoint_eq_infty_iff`: it sends exactly the boundary of the cube to `∞`.
* `TauCeti.cubeToOnePoint_surjective`: it is surjective when `N` is nonempty.
* `TauCeti.eq_or_mem_boundary_of_cubeToOnePoint_eq`: its fibres off `∞` are single points.
-/

public section

noncomputable section

open Metric OnePoint Set Topology Topology.Homotopy
open scoped unitInterval

namespace TauCeti

variable (N : Type*) [Fintype N]

/-- The cube `I^N` with its boundary collapsed to `∞` in `OnePoint (N → ℝ)`: the cube is the
closed unit ball of the sup norm on `N → ℝ`, collapsed by `TauCeti.unitBallToOnePoint`. -/
def cubeToOnePoint : C((N → I), OnePoint (N → ℝ)) where
  toFun z := unitBallToOnePoint (cubeHomeomorphClosedBall N z : N → ℝ)
  continuous_toFun :=
    continuousOn_unitBallToOnePoint.comp_continuous
      (continuous_subtype_val.comp (cubeHomeomorphClosedBall N).continuous)
      fun z => (cubeHomeomorphClosedBall N z).2

variable {N}

@[simp]
theorem cubeToOnePoint_apply (z : N → I) :
    cubeToOnePoint N z = unitBallToOnePoint (cubeHomeomorphClosedBall N z : N → ℝ) := by
  rw [cubeToOnePoint]
  rfl

/-- The collapse of the cube sends a point to `∞` exactly when it lies on the boundary. -/
theorem cubeToOnePoint_eq_infty_iff (z : N → I) :
    cubeToOnePoint N z = ∞ ↔ z ∈ Cube.boundary N := by
  rw [← norm_cubeHomeomorphClosedBall_eq_one_iff]
  rw [cubeToOnePoint_apply, unitBallToOnePoint_apply_eq_infty_iff]
  exact ⟨fun h => le_antisymm (mem_closedBall_zero_iff.1 (cubeHomeomorphClosedBall N z).2) h,
    fun h => h.ge⟩

/-- The collapse of the cube is surjective when the cube has positive dimension. -/
theorem cubeToOnePoint_surjective [Nonempty N] : Function.Surjective (cubeToOnePoint N) := by
  intro y
  obtain ⟨x, hx, rfl⟩ := image_unitBallToOnePoint_closedBall.ge (mem_univ y)
  exact ⟨(cubeHomeomorphClosedBall N).symm ⟨x, hx⟩, by simp⟩

/-- Two points with the same image under the collapse of the cube are equal or both on the
boundary. -/
theorem eq_or_mem_boundary_of_cubeToOnePoint_eq {z z' : N → I}
    (h : cubeToOnePoint N z = cubeToOnePoint N z') :
    z = z' ∨ (z ∈ Cube.boundary N ∧ z' ∈ Cube.boundary N) := by
  by_cases hz : z ∈ Cube.boundary N
  · exact Or.inr ⟨hz, (cubeToOnePoint_eq_infty_iff z').1
      (h.symm.trans ((cubeToOnePoint_eq_infty_iff z).2 hz))⟩
  · refine Or.inl ?_
    have hz' : z' ∉ Cube.boundary N := fun hz' =>
      hz ((cubeToOnePoint_eq_infty_iff z).1
        (h.trans ((cubeToOnePoint_eq_infty_iff z').2 hz')))
    have hlt (w : N → I) (hw : w ∉ Cube.boundary N) :
        ‖(cubeHomeomorphClosedBall N w : N → ℝ)‖ < 1 :=
      lt_of_le_of_ne (mem_closedBall_zero_iff.1 (cubeHomeomorphClosedBall N w).2)
        fun h1 => hw ((norm_cubeHomeomorphClosedBall_eq_one_iff w).1 h1)
    rw [cubeToOnePoint_apply, cubeToOnePoint_apply] at h
    rw [unitBallToOnePoint_apply_of_norm_lt (hlt z hz),
      unitBallToOnePoint_apply_of_norm_lt (hlt z' hz'), OnePoint.coe_eq_coe] at h
    have hx := OpenPartialHomeomorph.univUnitBall.symm.injOn
      (mem_ball_zero_iff.2 (hlt z hz)) (mem_ball_zero_iff.2 (hlt z' hz')) h
    exact (cubeHomeomorphClosedBall N).injective (Subtype.ext hx)

end TauCeti
