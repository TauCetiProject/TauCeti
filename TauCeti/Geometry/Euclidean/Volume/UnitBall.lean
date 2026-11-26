/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The volume `ω_k` of the unit ball of `ℝ ^ k`

This file defines `ω_k = TauCeti.unitBallVolume k`, the volume of the unit ball of
`EuclideanSpace ℝ (Fin k)`, and expresses the volume of every ball of radius `r` in a
`k`-dimensional real inner product space as `ω_k r ^ k`
(`TauCeti.volume_ball_eq_unitBallVolume_mul`, `TauCeti.volume_closedBall_eq_unitBallVolume_mul`).
It records `ω_1 = 2` and `ω_2 = π` (`TauCeti.unitBallVolume_one`, `TauCeti.unitBallVolume_two`).
The constant `ω_k` normalizes the `k`-dimensional densities of a measure.
-/

public section

noncomputable section

open Metric MeasureTheory Module
open scoped ENNReal

namespace TauCeti

/-- `ω_k`, the volume of the unit ball of `ℝ ^ k` (that is, of `EuclideanSpace ℝ (Fin k)`). The
volume of a ball of radius `r > 0` in a `k`-dimensional real inner product space is `ω_k r ^ k`
(`TauCeti.volume_ball_eq_unitBallVolume_mul`). -/
def unitBallVolume (k : ℕ) : ℝ≥0∞ :=
  volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1)

theorem unitBallVolume_def (k : ℕ) :
    unitBallVolume k = volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  (rfl)

theorem unitBallVolume_pos (k : ℕ) : 0 < unitBallVolume k :=
  measure_ball_pos _ _ one_pos

theorem unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 :=
  (unitBallVolume_pos k).ne'

theorem unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  measure_ball_lt_top.ne

/-- The volume `ω_k ρ ^ k` of a ball of radius `ρ > 0` in `ℝ ^ k` is nonzero. -/
theorem unitBallVolume_mul_ofReal_pow_ne_zero (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    unitBallVolume k * ENNReal.ofReal ρ ^ k ≠ 0 :=
  mul_ne_zero (unitBallVolume_ne_zero k) (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ).ne')

/-- The volume `ω_k ρ ^ k` of a ball of radius `ρ` in `ℝ ^ k` is finite. -/
theorem unitBallVolume_mul_ofReal_pow_ne_top (k : ℕ) (ρ : ℝ) :
    unitBallVolume k * ENNReal.ofReal ρ ^ k ≠ ∞ :=
  ENNReal.mul_ne_top (unitBallVolume_ne_top k) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The unit ball of a real inner product space of dimension `k` has volume `ω_k`. -/
theorem volume_ball_zero_one_eq_unitBallVolume :
    volume (ball (0 : E) 1) = unitBallVolume (finrank ℝ E) :=
  volume_ball_eq_of_finrank_eq (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm 0 0 1

/-- A closed ball of radius `r ≥ 0` in a real inner product space of dimension `k` has volume
`ω_k r ^ k`. -/
theorem volume_closedBall_eq_unitBallVolume_mul (x : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = unitBallVolume (finrank ℝ E) * ENNReal.ofReal r ^ finrank ℝ E := by
  rw [Measure.addHaar_closedBall _ x hr, volume_ball_zero_one_eq_unitBallVolume,
    ENNReal.ofReal_pow hr, mul_comm]

/-- An open ball of radius `r > 0` in a real inner product space of dimension `k` has volume
`ω_k r ^ k`. -/
theorem volume_ball_eq_unitBallVolume_mul (x : E) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = unitBallVolume (finrank ℝ E) * ENNReal.ofReal r ^ finrank ℝ E := by
  rw [Measure.addHaar_ball_of_pos _ x hr, volume_ball_zero_one_eq_unitBallVolume,
    ENNReal.ofReal_pow hr.le, mul_comm]

end InnerProductSpace

/-- `ω_1 = 2`: the unit ball of `ℝ` is an interval of length `2`. -/
@[simp]
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  have h := volume_ball_eq_unitBallVolume_mul (0 : ℝ) one_pos
  simp only [Real.volume_ball, Module.finrank_self, ENNReal.ofReal_one, one_pow, mul_one] at h
  rw [← h, ENNReal.ofReal_ofNat]

/-- `ω_2 = π`: the unit disc has area `π`. -/
@[simp]
theorem unitBallVolume_two : unitBallVolume 2 = ENNReal.ofReal Real.pi := by
  rw [unitBallVolume_def, EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_one, one_pow,
    one_mul]

end TauCeti
