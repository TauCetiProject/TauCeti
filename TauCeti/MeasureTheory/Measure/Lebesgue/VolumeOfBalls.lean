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
form used in normalizing constants.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module Real

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

end TauCeti
