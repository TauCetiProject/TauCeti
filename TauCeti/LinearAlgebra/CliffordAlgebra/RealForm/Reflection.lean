/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Coordinate reflections of the positive-definite real Clifford form

The reflection of `ℝⁿ` in the `i`-th coordinate hyperplane negates the `i`-th coordinate and fixes
the others. It is the quadratic reflection `QuadraticMap.reflection` in the coordinate vector
`Pi.single i 1`, an isometry of the positive-definite form `realCliffordForm n 0`, and it has
determinant `-1`.

## Main definitions

* `TauCeti.realCliffordCoordReflection`: the reflection of `ℝⁿ` in a coordinate hyperplane.

## Main results

* `TauCeti.realCliffordCoordReflection_apply`: the reflection negates the `i`-th coordinate.
* `TauCeti.det_realCliffordCoordReflection`: the reflection has determinant `-1`.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-- The **reflection of `ℝⁿ` in the `i`-th coordinate hyperplane**, negating the `i`-th
coordinate (`TauCeti.realCliffordCoordReflection_apply`): the reflection
`QuadraticMap.reflection` in the coordinate vector `Pi.single i 1`, as an isometry of the
positive-definite form `realCliffordForm n 0`. Its determinant is `-1`
(`TauCeti.det_realCliffordCoordReflection`), so it reverses orientation. -/
noncomputable def realCliffordCoordReflection (i : Fin n) :
    (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0) :=
  letI : Invertible (realCliffordForm n 0 (Pi.single i 1)) := invertibleOfNonzero (by simp)
  QuadraticMap.orthogonalGroupEquivIsometryEquiv _
    (QuadraticMap.reflectionOrthogonal _ (Pi.single i 1))

/-- The reflection in a coordinate hyperplane is the reflection in the coordinate vector. -/
theorem coe_realCliffordCoordReflection (i : Fin n) :
    letI : Invertible (realCliffordForm n 0 (Pi.single i 1)) := invertibleOfNonzero (by simp)
    ⇑(realCliffordCoordReflection i) =
      ⇑(QuadraticMap.reflection (realCliffordForm n 0) (Pi.single i 1)) := by
  simp only [realCliffordCoordReflection, QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv,
    QuadraticMap.coe_reflectionOrthogonal]

/-- The reflection in the `i`-th coordinate hyperplane negates the `i`-th coordinate and fixes
the others. -/
@[simp]
theorem realCliffordCoordReflection_apply (i : Fin n) (v : Fin n → ℝ) :
    realCliffordCoordReflection i v = Function.update v i (-v i) := by
  let _ : Invertible (realCliffordForm n 0 (Pi.single i 1)) := invertibleOfNonzero (by simp)
  rw [coe_realCliffordCoordReflection, QuadraticMap.reflection_apply, QuadraticMap.polar_comm,
    polar_realCliffordForm_single, realCliffordWeight_of_lt i.isLt, invOf_eq_inv,
    realCliffordForm_zero_single_one]
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
    ring
  · simp [hj]

/-- The reflection in a coordinate hyperplane has determinant `-1`. -/
@[simp]
theorem det_realCliffordCoordReflection (i : Fin n) :
    LinearMap.det ((realCliffordCoordReflection i).toLinearEquiv :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = -1 := by
  rw [realCliffordCoordReflection, QuadraticMap.toLinearEquiv_orthogonalGroupEquivIsometryEquiv,
    ← LinearEquiv.coe_det, ← QuadraticMap.orthogonalDet_apply,
    QuadraticMap.orthogonalDet_reflectionOrthogonal]
  simp

/-- The reflection in a coordinate hyperplane is an involution. -/
@[simp]
theorem realCliffordCoordReflection_symm (i : Fin n) :
    (realCliffordCoordReflection i).symm = realCliffordCoordReflection i :=
  DFunLike.ext _ _ fun v ↦ (realCliffordCoordReflection i).symm_apply_eq.mpr <| funext fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]

end TauCeti
