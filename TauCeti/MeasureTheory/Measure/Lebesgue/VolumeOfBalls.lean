/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The real volume of the unit ball

Mathlib computes the volume of a ball in a finite-dimensional real inner product space as an
extended nonnegative real (`InnerProductSpace.volume_ball`). This file records the real volume of
the unit ball in the form `π ^ (d / 2) / Γ(d / 2 + 1)`, where `d` is the dimension, which is the
form used in normalizing constants. It also shows that every finite-dimensional real inner
product space has a closed ball of volume one about the origin, and that a closed ball of
radius `r` in a one-dimensional space has volume `2 * r`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module Real Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The real volume of the unit ball of a nontrivial real inner product space of dimension `d` is
`π ^ (d / 2) / Γ(d / 2 + 1)`. -/
theorem volume_real_unitBall :
    volume.real (ball (0 : V) 1) =
      π ^ ((finrank ℝ V : ℝ) / 2) / Gamma (finrank ℝ V / 2 + 1) := by
  rw [measureReal_def, InnerProductSpace.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul pi_pos.le]
  ring_nf

omit [Nontrivial V] in
/-- There is a closed ball about the origin of volume one. -/
theorem exists_volume_closedBall_eq_one : ∃ ρ : ℝ, 0 < ρ ∧ volume (closedBall (0 : V) ρ) = 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- In the zero space every closed ball is the whole space, the unit parallelepiped.
    refine ⟨1, one_pos, ?_⟩
    have hpar := (stdOrthonormalBasis ℝ V).volume_parallelepiped
    rwa [Subsingleton.eq_univ_of_nonempty ⟨0, (mem_parallelepiped_iff _ _).2 ⟨0, by simp, by simp⟩⟩,
      ← Subsingleton.eq_univ_of_nonempty (nonempty_closedBall.2 zero_le_one)] at hpar
  -- Otherwise rescale the unit ball by `vol (ball 0 1) ^ (-1 / n)`.
  set n := finrank ℝ V
  set v := volume.real (ball (0 : V) 1)
  have hv : 0 < v :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hn : n ≠ 0 := finrank_pos.ne'
  refine ⟨v⁻¹ ^ (n⁻¹ : ℝ), by positivity, ?_⟩
  have hpow : (v⁻¹ ^ (n⁻¹ : ℝ)) ^ n = v⁻¹ := rpow_inv_natCast_pow (inv_nonneg.2 hv.le) hn
  have hinv : ENNReal.ofReal v⁻¹ = (volume (ball (0 : V) 1))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hv, ofReal_measureReal measure_ball_lt_top.ne]
  rw [Measure.addHaar_closedBall volume 0 (by positivity), hpow, hinv,
    ENNReal.inv_mul_cancel (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne]

omit [Nontrivial V] in
/-- In a one-dimensional real inner product space, a closed ball of radius `r ≥ 0` has volume
`2 * r`. -/
theorem volume_real_closedBall_of_finrank_eq_one (h : finrank ℝ V = 1) (x : V) {r : ℝ}
    (hr : 0 ≤ r) : volume.real (closedBall x r) = 2 * r := by
  rw [measureReal_def, InnerProductSpace.volume_closedBall_of_dim_odd (k := 0) h, h]
  simp [ENNReal.toReal_ofReal hr, mul_comm]

end TauCeti
