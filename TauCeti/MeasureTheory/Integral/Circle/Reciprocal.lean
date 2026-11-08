/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Circular averages of the reciprocal kernel

The angular average of `(w - z)⁻¹` on a centered circle is `w⁻¹` when the pole is outside and
zero when it is inside. The radius equal to the distance to the pole is deliberately excluded:
its angular slice is generally not integrable.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace TauCeti

/-- The flat angular average of the Cauchy kernel on a circle, away from the exceptional
radius meeting its pole. The value at a zero pole is included. -/
theorem integral_circleMap_sub_inv {w : ℂ} {r : ℝ} (hr : 0 < r) (hne : ‖w‖ ≠ r) :
    (∫ θ in 0..2 * π, (w - circleMap 0 r θ)⁻¹) =
      if r < ‖w‖ then (2 * π : ℂ) / w else 0 := by
  have hz : ∀ z ∈ sphere (0 : ℂ) r, z ≠ 0 := by
    intro z hz hz0
    exact hr.ne (by simpa [hz0] using (mem_sphere_iff_norm.mp hz))
  have hzw : ∀ z ∈ sphere (0 : ℂ) r, z - w ≠ 0 := by
    intro z hz heq
    exact hne (by simpa [sub_eq_zero.mp heq] using mem_sphere_iff_norm.mp hz)
  have hangle : (∮ z in C(0, r), z⁻¹ * (w - z)⁻¹) =
      I * ∫ θ in 0..2 * π, (w - circleMap 0 r θ)⁻¹ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, smul_eq_mul]
    have hθ := hz _ (circleMap_mem_sphere 0 hr.le θ)
    field_simp
  by_cases hw : w = 0
  · subst w
    have hpow : (∮ z in C(0, r), z⁻¹ * (0 - z)⁻¹) = 0 := by
      calc
        _ = ∮ z in C(0, r), (-1 : ℂ) * (z - 0)^(-2 : ℤ) := by
          apply circleIntegral.integral_congr hr.le
          intro z _
          simp [zpow_neg, pow_two]
        _ = -(∮ z in C(0, r), (z - 0)^(-2 : ℤ)) := by
          rw [circleIntegral.integral_const_mul]
          ring
        _ = 0 := by rw [circleIntegral.integral_sub_zpow_of_ne (by decide)]; simp
    rw [hangle] at hpow
    have hzero := (mul_eq_zero.mp hpow).resolve_left I_ne_zero
    simpa [hr.not_gt] using hzero
  · have h0 : CircleIntegrable (fun z : ℂ => z⁻¹) 0 r := by
      simpa only [sub_zero] using (circleIntegrable_sub_inv_iff (c := 0) (w := 0) (R := r)).mpr
        (Or.inr (by simpa [abs_of_pos hr] using (ne_of_lt hr)))
    have h1 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹) 0 r :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr (by simpa [abs_of_pos hr] using hne))
    have hsplit : (∮ z in C(0, r), z⁻¹ * (w - z)⁻¹) =
        w⁻¹ * ((2 * π * I : ℂ) - ∮ z in C(0, r), (z - w)⁻¹) := by
      calc
        _ = ∮ z in C(0, r), w⁻¹ * (z⁻¹ - (z - w)⁻¹) := by
          apply circleIntegral.integral_congr hr.le
          intro z hz'
          have hz0 := hz z hz'
          have hzw0 := hzw z hz'
          have hwz0 : w - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hzw0).symm
          field_simp [hw, hz0, hzw0, hwz0]
          ring
        _ = _ := by
          rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub h0 h1]
          simpa only [sub_zero] using congrArg (fun v => w⁻¹ * (v - ∮ z in C(0,r), (z - w)⁻¹))
            (circleIntegral.integral_sub_center_inv 0 hr.ne')
    rw [hangle] at hsplit
    by_cases hwr : r < ‖w‖
    · rw [TauCeti.Contour.circleIntegral_sub_inv_eq_zero_of_lt_dist hr.le
        (by simpa only [dist_zero_right] using hwr), sub_zero] at hsplit
      rw [ite_eq_left hwr]
      apply mul_left_cancel₀ I_ne_zero
      rw [hsplit]
      field_simp
    · have hwball : w ∈ ball (0 : ℂ) r := by
        simpa using lt_of_le_of_ne (not_lt.mp hwr) hne
      rw [circleIntegral.integral_sub_inv_of_mem_ball hwball, sub_self, mul_zero] at hsplit
      simpa [hwr] using (mul_eq_zero.mp hsplit).resolve_left I_ne_zero

/-- The same angular mean on the symmetric polar interval. -/
theorem integral_neg_pi_pi_circleMap_sub_inv {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hne : ‖w‖ ≠ r) :
    (∫ θ in -π..π, (w - circleMap 0 r θ)⁻¹) =
      if r < ‖w‖ then (2 * π : ℂ) / w else 0 := by
  have hp := ((periodic_circleMap 0 r).comp (fun z : ℂ => (w - z)⁻¹)).intervalIntegral_add_eq
    (-π) 0
  have heq : -π + 2 * π = π := by ring
  rw [heq, zero_add] at hp
  exact hp.trans (integral_circleMap_sub_inv hr hne)

end TauCeti
