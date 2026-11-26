/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Topology.MetricSpace.Holder

/-!
# The cutoff of a closed ball

For a point `x₀` of a pseudometric space and a radius `r`, the cutoff
`TauCeti.ballCutoff x₀ r x = projIcc 0 1 (2 - dist x x₀ / r)` takes values in `[0, 1]`. For
`r > 0` it is `1` on `closedBall x₀ r` (`TauCeti.ballCutoff_eq_one_of_mem_closedBall`) and `0` off
the doubled ball (`TauCeti.ballCutoff_eq_zero_of_two_mul_le_dist`). It is `|r|⁻¹`-Lipschitz
(`TauCeti.lipschitzWith_ballCutoff`), hence Hölder of every exponent at most one
(`TauCeti.holderWith_ballCutoff`).
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {x₀ x : X} {r : ℝ}

/-- The cutoff of the closed ball `closedBall x₀ r`, `x ↦ projIcc 0 1 (2 - dist x x₀ / r)`: for
`r > 0` it is `1` on the ball, `0` off the doubled ball and `r⁻¹`-Lipschitz, with values in
`[0, 1]`. -/
noncomputable def ballCutoff (x₀ : X) (r : ℝ) (x : X) : ℝ :=
  (projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r) : ℝ)

theorem ballCutoff_apply (x₀ : X) (r : ℝ) (x : X) :
    ballCutoff x₀ r x = projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r) := by
  rw [ballCutoff]

/-- The ball cutoff is `1` on its closed ball. -/
theorem ballCutoff_eq_one_of_mem_closedBall (hr : 0 < r) (hx : x ∈ closedBall x₀ r) :
    ballCutoff x₀ r x = 1 := by
  have hone : 1 ≤ 2 - dist x x₀ / r := by
    rw [le_sub_comm, div_le_iff₀ hr]
    linarith [mem_closedBall.mp hx]
  rw [ballCutoff, projIcc_of_right_le _ hone]

/-- The ball cutoff vanishes off the doubled ball. -/
theorem ballCutoff_eq_zero_of_two_mul_le_dist (hr : 0 < r) (hx : 2 * r ≤ dist x x₀) :
    ballCutoff x₀ r x = 0 := by
  have hneg : 2 - dist x x₀ / r ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hr]
    linarith
  rw [ballCutoff, projIcc_of_le_left _ hneg]

/-- The ball cutoff takes values in `[0, 1]`. -/
theorem ballCutoff_mem_Icc (x₀ : X) (r : ℝ) (x : X) : ballCutoff x₀ r x ∈ Icc 0 1 :=
  ballCutoff_apply x₀ r x ▸ Subtype.prop _

/-- The ball cutoff is nonnegative. -/
theorem ballCutoff_nonneg (x₀ : X) (r : ℝ) (x : X) : 0 ≤ ballCutoff x₀ r x :=
  (ballCutoff_mem_Icc x₀ r x).1

/-- The ball cutoff is at most `1`. -/
theorem ballCutoff_le_one (x₀ : X) (r : ℝ) (x : X) : ballCutoff x₀ r x ≤ 1 :=
  (ballCutoff_mem_Icc x₀ r x).2

/-- The norm of the ball cutoff is at most `1`. -/
theorem norm_ballCutoff_le (x₀ : X) (r : ℝ) (x : X) : ‖ballCutoff x₀ r x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (ballCutoff_nonneg x₀ r x)]
  exact ballCutoff_le_one x₀ r x

/-- The ball cutoff of radius `r` is `|r|⁻¹`-Lipschitz. -/
theorem lipschitzWith_ballCutoff (x₀ : X) (r : ℝ) : LipschitzWith ‖r‖₊⁻¹ (ballCutoff x₀ r) := by
  have hlin : LipschitzWith ‖r‖₊⁻¹ fun x : X ↦ 2 - dist x x₀ / r :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, NNReal.coe_inv, coe_nnNorm, Real.norm_eq_abs,
        show 2 - dist x x₀ / r - (2 - dist y x₀ / r) = r⁻¹ * (dist y x₀ - dist x x₀) by ring,
        abs_mul, abs_inv, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y x₀) (inv_nonneg.2 (abs_nonneg r))
  have h := (LipschitzWith.subtypeVal _).comp ((LipschitzWith.projIcc (zero_le_one' ℝ)).comp hlin)
  rw [one_mul, one_mul] at h
  exact h

/-- The ball cutoff of radius `r` is `α`-Hölder with constant `|r|⁻¹ + 2` for every exponent
`α ≤ 1`. -/
theorem holderWith_ballCutoff (x₀ : X) (r : ℝ) {α : ℝ≥0} (hα : α ≤ 1) :
    HolderWith (‖r‖₊⁻¹ + 2) α (ballCutoff x₀ r) := by
  have h := (lipschitzWith_ballCutoff x₀ r).lipschitzOnWith (s := univ).holderOnWith_of_norm_le
    (M := 1) (fun x _ ↦ (norm_ballCutoff_le x₀ r x).trans_eq NNReal.coe_one.symm) hα
  rw [mul_one] at h
  exact holderOnWith_univ.mp h

end TauCeti
