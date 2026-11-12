/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Circle integration on continuous boundary functions

`TauCeti.circleIntegralCLM` integrates a continuous function on the circle, viewed as a
subtype of `ℂ`. Its operator norm is bounded by the circumference. This permits limits and
power series in the uniform norm on the boundary to be integrated by continuous linear
mapping, without choosing continuous extensions away from the circle.

The radius may be negative or zero, as for Mathlib's `circleIntegral`.
-/

public section

open Complex MeasureTheory Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem intervalIntegrable_boundary (c : ℂ) (R : ℝ)
    (f : C(sphere c |R|, E)) :
    IntervalIntegrable (fun θ => deriv (circleMap c R) θ •
      f ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩) volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  simp only [deriv_circleMap]
  exact ((continuous_circleMap 0 R).mul_const I).smul
    (f.continuous.comp ((continuous_circleMap c R).subtype_mk _))

/-- Circle integration as a continuous complex linear map on continuous boundary functions.
For an incomplete codomain, this is the zero map, as Mathlib defines its integral to be zero. -/
noncomputable def circleIntegralCLM (c : ℂ) (R : ℝ) : C(sphere c |R|, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ in 0..2 * Real.pi, deriv (circleMap c R) θ •
        f ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, smul_add]
        exact intervalIntegral.integral_add (intervalIntegrable_boundary c R f)
          (intervalIntegrable_boundary c R g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_comm _ a]
        exact intervalIntegral.integral_smul a _ }
    (2 * Real.pi * |R|) fun f => by
      calc
        _ ≤ |R| * ‖f‖ * |2 * Real.pi - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
            simp only [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero,
              norm_I, mul_one]
            exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg R)
        _ = _ := by rw [sub_zero, abs_of_pos Real.two_pi_pos]; ring

/-- The boundary integral is the usual integral in the angular parametrization. -/
theorem circleIntegralCLM_apply (c : ℂ) (R : ℝ) (f : C(sphere c |R|, E)) :
    circleIntegralCLM c R f = ∫ θ in 0..2 * Real.pi, deriv (circleMap c R) θ •
      f ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩ := (rfl)

/-- Any ambient function agreeing with the boundary data has the same circle integral. -/
theorem circleIntegralCLM_eq_circleIntegral (c : ℂ) (R : ℝ)
    (f : C(sphere c |R|, E)) (g : ℂ → E) (hg : ∀ z, f z = g z) :
    circleIntegralCLM c R f = ∮ z in C(c, R), g z := by
  simp only [circleIntegralCLM_apply, hg, circleIntegral]

/-- The operator norm of circle integration is at most the circumference. -/
theorem norm_circleIntegralCLM_le (c : ℂ) (R : ℝ) :
    ‖circleIntegralCLM (E := E) c R‖ ≤ 2 * Real.pi * |R| := by
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- Circle integration on a circle of radius zero is the zero operator. -/
@[simp]
theorem circleIntegralCLM_zero_radius (c : ℂ) : circleIntegralCLM (E := E) c 0 = 0 := by
  ext f
  simp only [circleIntegralCLM_apply, deriv_circleMap]
  simp

end TauCeti
