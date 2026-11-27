/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The angle between unit vectors

For unit vectors `x` and `y` of a real inner product space, the unoriented angle `∠ x y` is
`arccos ⟪x, y⟫`: the normalising factor `‖x‖ * ‖y‖` in the definition of the angle is `1`.

## Main results

* `InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one`: the angle between unit vectors is
  the arccosine of their inner product.
-/

public section

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The angle between unit vectors `x` and `y` is `arccos ⟪x, y⟫`. This is the inverse of
`InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one`. -/
theorem angle_eq_arccos_inner_of_norm_eq_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = Real.arccos (inner ℝ x y) := by
  rw [inner_eq_cos_angle_of_norm_eq_one hx hy,
    Real.arccos_cos (angle_nonneg x y) (angle_le_pi x y)]

end InnerProductGeometry
