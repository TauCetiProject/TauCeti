/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Energy and oriented area of a complex-linear map between planes

For a real-linear map commuting with the positive right-angle rotations, the squared norms
of its differential on a rotated pair sum to twice its oriented area on that pair. The identity
also holds for the zero map, which is the pointwise model for a branch point.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Orientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (Module.finrank ℝ W = 2)]

/-- The squared norm in an oriented real plane is the sum of the squared projections onto
a unit vector and its positive right-angle rotation. -/
theorem norm_sq_eq_inner_sq_add_inner_rightAngleRotation_sq
    (o : Orientation ℝ V (Fin 2)) (v w : V) (hv : ‖v‖ = 1) :
    ‖w‖ ^ 2 = inner ℝ w v ^ 2 + inner ℝ w (o.rightAngleRotation v) ^ 2 := by
  have h := o.inner_sq_add_areaForm_sq v w
  rw [← o.inner_rightAngleRotation_left, hv, one_pow, one_mul] at h
  rw [real_inner_comm w v, real_inner_comm w (o.rightAngleRotation v)] at h
  exact h.symm

/-- For a complex-linear map of oriented real planes, twice the oriented area of the image
of a rotated pair is its total squared differential norm on that pair. -/
theorem two_mul_areaForm_map_eq_norm_sq_add_norm_sq
    (o : Orientation ℝ V (Fin 2)) (o' : Orientation ℝ W (Fin 2))
    (F : V →ₗ[ℝ] W)
    (hF : ∀ v, F (o.rightAngleRotation v) = o'.rightAngleRotation (F v))
    (v : V) :
    2 * o'.areaForm (F v) (F (o.rightAngleRotation v)) =
      ‖F v‖ ^ 2 + ‖F (o.rightAngleRotation v)‖ ^ 2 := by
  rw [hF v, o'.areaForm_rightAngleRotation_right,
    real_inner_self_eq_norm_sq, o'.rightAngleRotation.norm_map]
  ring

/-- A complex-linear map between oriented Euclidean planes is conformal. Its metric factor
is the squared norm of the image of any unit vector. -/
theorem inner_map_map_eq_norm_sq_mul_inner
    (o : Orientation ℝ V (Fin 2)) (o' : Orientation ℝ W (Fin 2))
    (F : V →ₗ[ℝ] W)
    (hF : ∀ v, F (o.rightAngleRotation v) = o'.rightAngleRotation (F v))
    (e : V) (he : ‖e‖ = 1) (v w : V) :
    inner ℝ (F v) (F w) = ‖F e‖ ^ 2 * inner ℝ v w := by
  have he0 : e ≠ 0 := by
    intro h
    simp [h] at he
  let b := o.basisRightAngleRotation e he0
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    ((innerₛₗ ℝ : W →ₗ[ℝ] W →ₗ[ℝ] ℝ).compl₂ F).comp F
  have hB : B = ‖F e‖ ^ 2 • (innerₛₗ ℝ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [B, b, o.coe_basisRightAngleRotation, hF e, he]
  exact congrArg (fun T : V →ₗ[ℝ] V →ₗ[ℝ] ℝ ↦ T v w) hB

end Orientation
