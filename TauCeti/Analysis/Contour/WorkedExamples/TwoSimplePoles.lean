/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Theorem
public import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# A circle integral with two simple poles

This file verifies the two-pole worked example from the contour-integration roadmap.  For two
distinct points `s₁` and `s₂`, the function

`z ↦ A / (z - s₁) + B / (z - s₂)`

has residues `A` and `B` at the respective poles.  When both poles lie inside a circle, its
contour integral is therefore `2πi (A + B)`.  The calculation is stated directly for arbitrary
centres, radii, pole positions, and coefficients, so it also covers a vanishing coefficient
without pretending that the corresponding point remains a pole.

The integral calculation uses Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`; the
residue calculations use the simple-pole API in
`TauCeti.Analysis.Contour.Residue.SimplePole`.

This is the concrete two-simple-pole acceptance criterion in
`TauCetiRoadmap/ContourIntegration/README.md`, under “Worked examples”.
-/

public section

noncomputable section

open Metric

namespace TauCeti.Contour

/-- The rational function with prescribed principal parts `A / (z - s₁)` and
`B / (z - s₂)`. -/
def twoSimplePoles (A B s₁ s₂ : ℂ) (z : ℂ) : ℂ :=
  A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹

/-- Away from its two designated points, `twoSimplePoles` is analytic. -/
theorem analyticAt_twoSimplePoles {A B s₁ s₂ z : ℂ} (hz₁ : z ≠ s₁) (hz₂ : z ≠ s₂) :
    AnalyticAt ℂ (twoSimplePoles A B s₁ s₂) z := by
  exact (analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
    (sub_ne_zero.2 hz₁))).add (analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hz₂)))

/-- The function `twoSimplePoles` is meromorphic everywhere. -/
theorem meromorphicAt_twoSimplePoles (A B s₁ s₂ z : ℂ) :
    MeromorphicAt (twoSimplePoles A B s₁ s₂) z := by
  exact (analyticAt_const.meromorphicAt.mul
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)).add
      (analyticAt_const.meromorphicAt.mul
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv))

/-- At the first of two distinct designated points, the residue of `twoSimplePoles` is the first
coefficient. -/
@[simp]
theorem residue_twoSimplePoles_left {A B s₁ s₂ : ℂ} (h : s₁ ≠ s₂) :
    residue (twoSimplePoles A B s₁ s₂) s₁ = A := by
  unfold twoSimplePoles
  have hf₁ : MeromorphicAt (fun z => A * (z - s₁)⁻¹) s₁ :=
    analyticAt_const.meromorphicAt.mul (meromorphicAt_sub_inv s₁)
  have hf₂ : MeromorphicAt (fun z => B * (z - s₂)⁻¹) s₁ :=
    analyticAt_const.meromorphicAt.mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  rw [show (fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹) =
    (fun z => A * (z - s₁)⁻¹) + (fun z => B * (z - s₂)⁻¹) by rfl]
  rw [residue_add hf₁ hf₂, residue_const_mul_sub_inv,
    residue_eq_zero_of_analyticAt]
  · simp
  · exact analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h))

/-- At the second of two distinct designated points, the residue of `twoSimplePoles` is the second
coefficient. -/
@[simp]
theorem residue_twoSimplePoles_right {A B s₁ s₂ : ℂ} (h : s₁ ≠ s₂) :
    residue (twoSimplePoles A B s₁ s₂) s₂ = B := by
  unfold twoSimplePoles
  have hf₁ : MeromorphicAt (fun z => A * (z - s₁)⁻¹) s₂ :=
    analyticAt_const.meromorphicAt.mul
      ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  have hf₂ : MeromorphicAt (fun z => B * (z - s₂)⁻¹) s₂ :=
    analyticAt_const.meromorphicAt.mul (meromorphicAt_sub_inv s₂)
  rw [show (fun z => A * (z - s₁)⁻¹ + B * (z - s₂)⁻¹) =
    (fun z => A * (z - s₁)⁻¹) + (fun z => B * (z - s₂)⁻¹) by rfl]
  rw [residue_add hf₁ hf₂, residue_const_mul_sub_inv,
    residue_eq_zero_of_analyticAt, zero_add]
  exact analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h.symm))

/-- A reciprocal simple pole strictly inside a circle is circle integrable. -/
private theorem circleIntegrable_const_mul_sub_inv {A c s : ℂ} {R : ℝ} (hs : s ∈ ball c R) :
    CircleIntegrable (fun z => A * (z - s)⁻¹) c R := by
  have hR : 0 < R := pos_of_mem_ball hs
  apply ContinuousOn.circleIntegrable hR.le
  have hne : ∀ z ∈ sphere c R, z - s ≠ 0 := by
    intro z hz
    exact sub_ne_zero.2 fun h => by
      subst z
      exact (ne_of_lt (mem_ball.1 hs)) (mem_sphere.1 hz)
  exact continuousOn_const.mul
    ((continuousOn_id.sub (continuousOn_const : ContinuousOn (fun _ : ℂ => s) (sphere c R))).inv₀
      hne)

/-- **Two-pole circle integral.** If `s₁` and `s₂` lie strictly inside the circle `C(c, R)`, then
the integral of `A / (z - s₁) + B / (z - s₂)` around that circle is `2πi (A + B)`.  Together with
`residue_twoSimplePoles_left` and `residue_twoSimplePoles_right`, this is the roadmap's worked
example of the classical residue theorem with two simple poles. -/
theorem circleIntegral_twoSimplePoles {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs₁ : s₁ ∈ ball c R) (hs₂ : s₂ ∈ ball c R) :
    circleIntegral (twoSimplePoles A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I * (A + B) := by
  unfold twoSimplePoles
  rw [circleIntegral.integral_add (circleIntegrable_const_mul_sub_inv hs₁)
    (circleIntegrable_const_mul_sub_inv hs₂), circleIntegral.integral_const_mul,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hs₁,
    circleIntegral.integral_sub_inv_of_mem_ball hs₂]
  ring

/-- The two-pole calculation in residue-theorem form: for distinct points inside the circle, the
integral is `2πi` times the sum of the two residues. -/
theorem circleIntegral_twoSimplePoles_eq_residue_sum {A B c s₁ s₂ : ℂ} {R : ℝ}
    (hs : s₁ ≠ s₂) (hs₁ : s₁ ∈ ball c R) (hs₂ : s₂ ∈ ball c R) :
    circleIntegral (twoSimplePoles A B s₁ s₂) c R =
      2 * (Real.pi : ℂ) * Complex.I *
        (residue (twoSimplePoles A B s₁ s₂) s₁ + residue (twoSimplePoles A B s₁ s₂) s₂) := by
  rw [circleIntegral_twoSimplePoles hs₁ hs₂, residue_twoSimplePoles_left hs,
    residue_twoSimplePoles_right hs]

end TauCeti.Contour

end
