/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Representation.Ball
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.BallPotential

/-!
# The Newtonian potential and the Green potential of the unit ball of `ℝ³`

Let `B` be the unit ball of `ℝ³` and `Φ(x) = 1 / (4π ‖x‖)` the Newtonian kernel. The Newtonian
potential `v(x) = ∫_B Φ(x - y) dy` of `B` is `(3 - ‖x‖²) / 6` on the closed ball, so `-Δv = 1`
in `B`, and `1 / (3 ‖x‖)` outside it. On the unit sphere it takes the value `1 / 3`, not `0`: the
uncorrected potential does not solve the Dirichlet problem `-Δu = 1` in `B`, `u = 0` on the sphere.
The harmonic function with boundary values `1 / 3` is the constant `1 / 3`, and the Green potential
of `1`, which does solve the Dirichlet problem, is `v - 1 / 3 = (1 - ‖x‖²) / 6`.

## Main declarations

* `TauCeti.Examples.UnitBallThree.setIntegral_ball_newtonianKernel_three_sub`: the Newtonian
  potential of the unit ball is `(3 - ‖x‖²) / 6` on the closed ball.
* `TauCeti.Examples.UnitBallThree.setIntegral_ball_newtonianKernel_three_sub_of_one_le_norm`: it
  is `1 / (3 ‖x‖)` outside the ball.
* `TauCeti.Examples.UnitBallThree.setIntegral_ball_newtonianKernel_three_sub_of_norm_eq_one`: it
  is `1 / 3` on the unit sphere.
* `TauCeti.Examples.UnitBallThree.ae_setIntegral_ballGreenKernel_three_eq`: the Green potential of
  `1` is `v - 1 / 3`.
-/

public section

namespace TauCeti.Examples.UnitBallThree

open MeasureTheory Metric

/-- **The Newtonian potential of the unit ball of `ℝ³`, inside.** On the closed unit ball,
`∫_B Φ(x - y) dy = (3 - ‖x‖²) / 6`. -/
theorem setIntegral_ball_newtonianKernel_three_sub {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ‖x‖ ≤ 1) :
    ∫ y in ball 0 1, newtonianKernel 3 (x - y) = (3 - ‖x‖ ^ 2) / 6 := by
  rw [setIntegral_ball_newtonianKernel_sub_of_norm_sub_le (by norm_num) (by rwa [sub_zero]),
    sub_zero]
  norm_num
  ring

/-- **The Newtonian potential of the unit ball of `ℝ³`, outside.** For `1 ≤ ‖x‖`,
`∫_B Φ(x - y) dy = 1 / (3 ‖x‖)`, the potential of the mass `4π / 3` of the ball placed at the
origin. -/
theorem setIntegral_ball_newtonianKernel_three_sub_of_one_le_norm
    {x : EuclideanSpace ℝ (Fin 3)} (hx : 1 ≤ ‖x‖) :
    ∫ y in ball 0 1, newtonianKernel 3 (x - y) = (3 * ‖x‖)⁻¹ := by
  have hx0 : ‖x‖ ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have h := pow_norm_mul_measureReal_ball_mul_newtonianKernel x
  rw [setIntegral_ball_newtonianKernel_sub_of_le_norm_sub (by rwa [sub_zero]), sub_zero]
  norm_num at h
  linear_combination (norm := (field_simp; ring)) h / ‖x‖ ^ 3

/-- **The Newtonian potential of the unit ball of `ℝ³` on the unit sphere** is the constant
`1 / 3`. In particular it does not vanish there, so it is not the solution of the Dirichlet
problem `-Δu = 1` in the ball, `u = 0` on the sphere. -/
theorem setIntegral_ball_newtonianKernel_three_sub_of_norm_eq_one
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) :
    ∫ y in ball 0 1, newtonianKernel 3 (x - y) = 1 / 3 := by
  rw [setIntegral_ball_newtonianKernel_three_sub hx.le, hx]
  norm_num

/-- **The Green potential of the unit ball of `ℝ³`.** The solution `(1 - ‖x‖²) / 6` of `-Δu = 1` in
the unit ball, `u = 0` on the sphere, is the Newtonian potential of the ball corrected by the
constant harmonic function `1 / 3`, the boundary value of the potential:
`∫_B G(x, y) dy = (1 - ‖x‖²) / 6 = ∫_B Φ(x - y) dy - 1 / 3` for almost every `x ∈ B`. -/
theorem ae_setIntegral_ballGreenKernel_three_eq :
    ∀ᵐ x ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)),
      ∫ y in ball 0 1, ballGreenKernel 3 x y = (1 - ‖x‖ ^ 2) / 6 ∧
        ∫ y in ball 0 1, ballGreenKernel 3 x y =
          (∫ y in ball 0 1, newtonianKernel 3 (x - y)) - 1 / 3 := by
  filter_upwards [ae_setIntegral_ballGreenKernel_eq (n := 2) (by norm_num),
    ae_setIntegral_ballGreenKernel_eq_setIntegral_newtonianKernel_sub (n := 2) (by norm_num)]
    with x hx hx'
  refine ⟨by rw [hx, PDE.ballTorsionFunction_apply]; norm_num, by rw [hx']; norm_num⟩

end TauCeti.Examples.UnitBallThree
