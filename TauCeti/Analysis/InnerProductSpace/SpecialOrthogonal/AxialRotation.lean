/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal

/-!
# The rotation angle of a rotation of `ℝ³` about an axis

In `ℝ³`, with coordinate vectors `e₀, e₁, e₂`, the special orthogonal transformations fixing `e₂`
(`TauCeti.specialOrthogonalStabilizer`) are the rotations of the plane `⟨e₀, e₁⟩`. Such a `g`
sends `e₀` to `a e₀ + b e₁` with `a² + b² = 1`, and then `e₁` to `-b e₀ + a e₁`
(`TauCeti.apply_single_one_one_eq_axialRotationAngle`): the column `g e₁` is a unit vector
orthogonal to `e₂` and `g e₀`, and the determinant `1` fixes its sign. The rotation angle `a + b i`
(`TauCeti.axialRotationAngle`) is therefore a continuous homomorphism `SO(2) → U(1)`.

## Main definitions

* `TauCeti.axialRotationAngle`: the rotation angle `U(1)` of a rotation of `ℝ³` about `e₂`.

## Main results

* `TauCeti.apply_single_zero_one_eq_axialRotationAngle`,
  `TauCeti.apply_single_one_one_eq_axialRotationAngle`: a rotation about `e₂` with angle `a + b i`
  sends `e₀` to `a e₀ + b e₁` and `e₁` to `-b e₀ + a e₁`.
* `TauCeti.continuous_axialRotationAngle`: the rotation angle is continuous.
-/

public section

noncomputable section

namespace TauCeti

/-- The Euclidean space `ℝ³`. -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The coordinate vector `e₂` of `ℝ³`, the axis of the rotations considered here. -/
local notation "e₂" => EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- The rotations of `ℝ³` about the axis `e₂`. -/
local notation "SO₂" => specialOrthogonalStabilizer E3 e₂

section Angle

variable (g : SO₂)

/-- The image `g e_j` of a coordinate vector under a rotation about `e₂`. -/
private abbrev col (j : Fin 3) : E3 := (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single j 1)

/-- `(g h) e_j = g (h e_j)`. -/
private theorem col_mul (h : SO₂) (j : Fin 3) : col (g * h) j = (g.val : E3 →L[ℝ] E3) (col h j) :=
  rfl

/-- A rotation about `e₂` preserves the inner products of coordinate vectors. -/
private theorem inner_col (i j : Fin 3) :
    inner ℝ (col g i) (col g j) = if i = j then 1 else 0 := by
  rw [Unitary.inner_map_map, EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]

/-- The last coordinate of `g e₀` and of `g e₁` vanishes. -/
private theorem col_two {j : Fin 3} (hj : j ≠ 2) : col g j 2 = 0 := by
  have h := inner_col g 2 j
  rw [col, (mem_specialOrthogonalStabilizer_iff.1 g.property).1,
    EuclideanSpace.inner_single_left] at h
  simpa [Ne.symm hj] using h

/-- `g e₂ = e₂`. -/
private theorem col_axis : col g 2 = e₂ :=
  (mem_specialOrthogonalStabilizer_iff.1 g.property).1

/-- The inner product of two vectors of `ℝ³` in coordinates. -/
private theorem inner_eq (x y : E3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The determinant of a rotation about `e₂` is the determinant `a d - b c` of its action on the
plane `⟨e₀, e₁⟩`. -/
private theorem det_eq :
    ((g.val : E3 →L[ℝ] E3) : E3 →ₗ[ℝ] E3).det = col g 0 0 * col g 1 1 - col g 1 0 * col g 0 1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe]
  have h2 := col_axis g
  have h20 := col_two g (j := 0) (by decide)
  have h21 := col_two g (j := 1) (by decide)
  simp only [col] at h2 h20 h21
  rw [h2, h20, h21]
  simp [col]

/-- **A rotation about `e₂` turns the plane `⟨e₀, e₁⟩`**: if `g e₀ = a e₀ + b e₁`, then
`g e₁ = -b e₀ + a e₁`. -/
private theorem col_one : col g 1 0 = -col g 0 1 ∧ col g 1 1 = col g 0 0 := by
  have h1 := inner_col g 0 0
  have h2 := inner_col g 0 1
  have h3 : col g 0 0 * col g 1 1 - col g 1 0 * col g 0 1 = 1 := by
    rw [← det_eq]
    exact (mem_specialOrthogonalStabilizer_iff.1 g.property).2
  simp only [inner_eq, col_two g (j := 0) (by decide), col_two g (j := 1) (by decide)] at h1 h2
  norm_num at h1 h2
  constructor
  · linear_combination (-col g 1 0) * h1 + col g 0 0 * h2 - col g 0 1 * h3
  · linear_combination (-col g 1 1) * h1 + col g 0 1 * h2 + col g 0 0 * h3

/-- The rotation angle `a + b i` of `g`, where `g e₀ = a e₀ + b e₁`, is a unit complex number. -/
private theorem norm_angle : ‖(col g 0 0 : ℂ) + col g 0 1 * Complex.I‖ = 1 := by
  have h := inner_col g 0 0
  simp only [inner_eq, col_two g (j := 0) (by decide)] at h
  norm_num at h
  rw [Complex.norm_add_mul_I, ← Real.sqrt_one]
  congr 1
  linear_combination h

/-- A rotation about `e₂` sends `e₀` to `a e₀ + b e₁`. -/
private theorem col_zero_eq : col g 0 = col g 0 0 • EuclideanSpace.single 0 1 +
    col g 0 1 • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [col_two g (j := 0) (by decide)]

/-- A rotation about `e₂` sends `e₁` to `-b e₀ + a e₁`. -/
private theorem col_one_eq : col g 1 = (-col g 0 1) • EuclideanSpace.single 0 1 +
    col g 0 0 • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [col_two g (j := 1) (by decide), (col_one g).1, (col_one g).2]

/-- The rotation angle `a + b i` of `g`, where `g e₀ = a e₀ + b e₁`, as a point of the circle. -/
private def angle : Circle :=
  ⟨(col g 0 0 : ℂ) + col g 0 1 * Complex.I, mem_sphere_zero_iff_norm.2 (norm_angle g)⟩

/-- The value of `angle g` in `ℂ`. -/
private theorem coe_angle : (angle g : ℂ) = (col g 0 0 : ℂ) + col g 0 1 * Complex.I :=
  rfl

/-- **The rotation angle** of a rotation `g` of `ℝ³` about `e₂`: the unit complex number
`a + b i`, where `g e₀ = a e₀ + b e₁`. It is a homomorphism, since `g` rotates the plane `⟨e₀, e₁⟩`
by `a + b i` (`TauCeti.apply_single_zero_one_eq_axialRotationAngle`,
`TauCeti.apply_single_one_one_eq_axialRotationAngle`). -/
def axialRotationAngle : SO₂ →* Circle where
  toFun := angle
  map_one' := by
    apply Circle.ext
    simp [coe_angle, col]
  map_mul' g h := by
    apply Circle.ext
    have hmul : col (g * h) 0 = col h 0 0 • col g 0 + col h 0 1 • col g 1 := by
      rw [col_mul]
      conv_lhs => rw [col_zero_eq h]
      rw [map_add, map_smul, map_smul]
    rw [Circle.coe_mul, coe_angle, coe_angle, coe_angle, hmul]
    apply Complex.ext <;>
      simp [(col_one g).1, (col_one g).2] <;> ring

/-- The rotation angle of `g` is `a + b i`, where `g e₀ = a e₀ + b e₁`. -/
@[simp]
theorem coe_axialRotationAngle :
    (axialRotationAngle g : ℂ) =
      ((g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) 0 : ℂ) +
        (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) 1 * Complex.I :=
  (rfl)

/-- **A rotation about `e₂` with angle `z` sends `e₀` to `Re z e₀ + Im z e₁`.** -/
theorem apply_single_zero_one_eq_axialRotationAngle :
    (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) =
      (axialRotationAngle g : ℂ).re • EuclideanSpace.single 0 1 +
        (axialRotationAngle g : ℂ).im • EuclideanSpace.single 1 1 := by
  simpa using col_zero_eq g

/-- **A rotation about `e₂` with angle `z` sends `e₁` to `-Im z e₀ + Re z e₁`.** -/
theorem apply_single_one_one_eq_axialRotationAngle :
    (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 1 1) =
      (-(axialRotationAngle g : ℂ).im) • EuclideanSpace.single 0 1 +
        (axialRotationAngle g : ℂ).re • EuclideanSpace.single 1 1 := by
  simpa using col_one_eq g

/-- The rotation angle is continuous on the rotations about `e₂`, with the operator-norm
topology. -/
@[fun_prop]
theorem continuous_axialRotationAngle : Continuous (axialRotationAngle : SO₂ → Circle) := by
  refine Continuous.subtype_mk ?_ fun g ↦ mem_sphere_zero_iff_norm.2 (norm_angle g)
  have hcol : Continuous fun g : SO₂ ↦ (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) :=
    (ContinuousLinearMap.apply ℝ E3 (EuclideanSpace.single 0 1)).continuous.comp
      (continuous_subtypeVal.comp continuous_subtypeVal)
  have h0 := (PiLp.continuous_apply 2 _ (0 : Fin 3)).comp hcol
  have h1 := (PiLp.continuous_apply 2 _ (1 : Fin 3)).comp hcol
  simp only [Function.comp_def] at h0 h1
  fun_prop

end Angle

end TauCeti
