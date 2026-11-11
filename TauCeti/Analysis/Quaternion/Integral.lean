/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import TauCeti.Analysis.Quaternion.Forms
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Polar coordinates on the quaternions

Integrals over the quaternions are taken on the coordinate space `Fin 4 → ℝ`, read as `ℍ`
through `dq`, with its product Lebesgue measure; no measure is placed on `ℍ` itself. This file
proves the polar formula `TauCeti.Quaternion.integral_fun_norm_dq_sub`:
`∫ x, f ‖dq x - q₀‖ = 2π² ∫₀^∞ y³ f y`, where `2π²` is the area of the unit `3`-sphere.

Radial variables are the Euclidean norm of `ℍ`, never the sup norm of the coordinate space.
The proof transports the coordinate space onto `EuclideanSpace ℝ (Fin 4)` by the
measure-preserving map `WithLp.toLp 2`, which is not an isometry for the sup norm;
`TauCeti.Quaternion.norm_dq` identifies the norm of `dq x` with the Euclidean norm of the
transported point. It then uses Mathlib's polar decomposition of Haar measure and the volume
`π² / 2` of the unit ball in dimension four.
-/

public section

open MeasureTheory Set Real
open scoped Quaternion

namespace TauCeti.Quaternion

/-- Polar coordinates on the quaternions, centred at `q₀` and read on the coordinate space:
the integral of a function of `‖dq x - q₀‖` is `2π²`, the area of the unit `3`-sphere, times
its radial integral against `y³`. No integrability is assumed: when one side is not
integrable, neither is the other and both are `0`. -/
theorem integral_fun_norm_dq_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (q₀ : ℍ) :
    ∫ x : Fin 4 → ℝ, f ‖dq x - q₀‖ = (2 * π ^ 2) • ∫ y in Ioi (0 : ℝ), y ^ 3 • f y := by
  obtain ⟨c, rfl⟩ : ∃ c, dq c = q₀ :=
    ⟨QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q₀, by simp [coe_dq]⟩
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) =
      π ^ 2 / 2 := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
    simp [Nat.factorial, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π ^ 2 / 2)]
  calc ∫ x : Fin 4 → ℝ, f ‖dq x - dq c‖
      = ∫ x : Fin 4 → ℝ, f ‖dq x‖ := by
        simpa only [map_sub] using integral_sub_right_eq_self (fun x ↦ f ‖dq x‖) c
    _ = ∫ y : EuclideanSpace ℝ (Fin 4), f ‖y‖ := by
        simp only [norm_dq]
        exact (PiLp.volume_preserving_toLp (Fin 4)).integral_comp
          (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding (fun y ↦ f ‖y‖)
    _ = (2 * π ^ 2) • ∫ y in Ioi (0 : ℝ), y ^ 3 • f y := by
        rw [integral_fun_norm_addHaar, finrank_euclideanSpace_fin, hball,
          ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        norm_num
        ring_nf

end TauCeti.Quaternion
