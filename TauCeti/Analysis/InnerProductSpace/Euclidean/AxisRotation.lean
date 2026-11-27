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
# The rotations of `ℝ³` about an axis

Write `e₀, e₁, e₂` for the standard basis of `ℝ³`. The **rotations about the first axis**,
`TauCeti.axisRotationGroup`, are the special orthogonal transformations fixing `e₀`, a copy of
`SO(2)` inside `SO(3)`. Such a `g` turns the plane `⟨e₁, e₂⟩`: if `g e₁ = a e₁ + b e₂`, then
`a² + b² = 1` and `g e₂ = -b e₁ + a e₂`, because `g e₂` is a unit vector orthogonal to `e₀` and
`g e₁`, and `det g = 1` (computed with `Matrix.det_fin_three`) fixes its sign. So `g` is determined
by its **angle** `a + b i`, a unit complex number, and `g ↦ a + b i` is a continuous homomorphism
`TauCeti.axisRotationAngle : SO(2) → U(1)` (`TauCeti.axisRotation_apply_one`,
`TauCeti.axisRotation_apply_two`, `TauCeti.continuous_axisRotationAngle`).

The `Spinᶜ(3)` lift of these rotations is `TauCeti.axisSpinCLift`, in
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.AxisRotation`.

## Main definitions

* `TauCeti.axisRotationGroup`: the rotations of `ℝ³` fixing `e₀`, a copy of `SO(2)`.
* `TauCeti.axisRotationAngle`: the angle `SO(2) → U(1)` of a rotation about the first axis.

## Main results

* `TauCeti.axisRotation_apply_zero`, `TauCeti.axisRotation_apply_one`,
  `TauCeti.axisRotation_apply_two`: a rotation about the first axis fixes the `e₀`-coordinate and
  turns the `e₁`- and `e₂`-coordinates by its angle.
* `TauCeti.continuous_axisRotationAngle`: the angle is continuous.
-/

public section

noncomputable section

namespace TauCeti

/-- The Euclidean space `ℝ³`. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The rotations of `ℝ³` about the first coordinate axis**: the orthogonal transformations
fixing the first standard basis vector `e₀` and of determinant `1`, a copy of `SO(2)`. -/
def axisRotationGroup : Subgroup (unitary (ℝ³ →L[ℝ] ℝ³)) :=
  MulAction.stabilizer _ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ⊓ specialOrthogonalGroup ℝ³

/-- The rotations about the first axis are the stabilizer of `e₀` in `SO(3)`. -/
theorem axisRotationGroup_def :
    axisRotationGroup =
      MulAction.stabilizer _ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ⊓
        specialOrthogonalGroup ℝ³ :=
  (rfl)

/-- An orthogonal transformation is a rotation about the first axis exactly when it fixes `e₀` and
has determinant `1`. -/
theorem mem_axisRotationGroup_iff {g : unitary (ℝ³ →L[ℝ] ℝ³)} :
    g ∈ axisRotationGroup ↔
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 0 1) = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∧
        (g : ℝ³ →L[ℝ] ℝ³).det = 1 := by
  rw [axisRotationGroup_def, Subgroup.mem_inf, mem_specialOrthogonalGroup_iff,
    MulAction.mem_stabilizer_iff, Submonoid.smul_def, ContinuousLinearMap.smul_def]

section Coordinates

variable {g : unitary (ℝ³ →L[ℝ] ℝ³)}

/-- The real inner product of `ℝ³` in coordinates. -/
private theorem inner_eq_coord (x y : ℝ³) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The coordinates of the images of `e₁` and `e₂` under a rotation about the first axis: the
images lie in the plane `⟨e₁, e₂⟩`, and if `g e₁ = (0, a, b)` then `a² + b² = 1` and
`g e₂ = (0, -b, a)`. -/
private theorem axisRotation_coords (hg : g ∈ axisRotationGroup) :
    (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 0 = 0 ∧
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 2 1) 0 = 0 ∧
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 1 ^ 2 +
        (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 2 ^ 2 = 1 ∧
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 2 1) 1 =
        -(g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 2 ∧
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 2 1) 2 =
        (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 1 := by
  obtain ⟨h0, hdet⟩ := mem_axisRotationGroup_iff.1 hg
  set G := (g : ℝ³ →L[ℝ] ℝ³)
  have hi : ∀ x y, inner ℝ (G x) (G y) = inner ℝ x y := Unitary.inner_map_map g
  have h10 : G (EuclideanSpace.single 1 1) 0 = 0 := by
    simpa [h0, inner_eq_coord] using hi (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)
  have h20 : G (EuclideanSpace.single 2 1) 0 = 0 := by
    simpa [h0, inner_eq_coord] using hi (EuclideanSpace.single 2 1) (EuclideanSpace.single 0 1)
  have h11 := hi (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
  have h22 := hi (EuclideanSpace.single 2 1) (EuclideanSpace.single 2 1)
  have h12 := hi (EuclideanSpace.single 1 1) (EuclideanSpace.single 2 1)
  rw [inner_eq_coord, inner_eq_coord] at h11 h22 h12
  simp only [h10, h20, PiLp.single_apply] at h11 h22 h12
  norm_num at h11 h22 h12
  have hd := hdet
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    Matrix.det_fin_three] at hd
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe, h0] at hd
  norm_num [h10, h20] at hd
  refine ⟨h10, h20, by linear_combination h11, ?_, ?_⟩
  · linear_combination (-G (EuclideanSpace.single 1 1) 2) * hd +
      G (EuclideanSpace.single 1 1) 1 * h12 - G (EuclideanSpace.single 2 1) 1 * h11
  · linear_combination G (EuclideanSpace.single 1 1) 1 * hd +
      G (EuclideanSpace.single 1 1) 2 * h12 - G (EuclideanSpace.single 2 1) 2 * h11

/-- The coordinates of `g v` for a rotation `g` about the first axis with `g e₁ = (0, a, b)`. -/
private theorem axisRotation_apply_coords (hg : g ∈ axisRotationGroup)
    (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 0 = v 0 ∧
      (g : ℝ³ →L[ℝ] ℝ³) v 1 =
        (g : ℝ³ →L[ℝ] ℝ³)
            (EuclideanSpace.single 1 1) 1 * v 1 -
          (g : ℝ³ →L[ℝ] ℝ³)
            (EuclideanSpace.single 1 1) 2 * v 2 ∧
      (g : ℝ³ →L[ℝ] ℝ³) v 2 =
        (g : ℝ³ →L[ℝ] ℝ³)
            (EuclideanSpace.single 1 1) 2 * v 1 +
          (g : ℝ³ →L[ℝ] ℝ³)
            (EuclideanSpace.single 1 1) 1 * v 2 := by
  obtain ⟨h10, h20, -, h21, h22⟩ := axisRotation_coords hg
  have h0 := (mem_axisRotationGroup_iff.1 hg).1
  set G := (g : ℝ³ →L[ℝ] ℝ³)
  have hv : v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 +
      v 2 • EuclideanSpace.single 2 1 := by
    ext i; fin_cases i <;> simp
  rw [hv]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, h0, h10, h20, h21,
    h22]
  norm_num
  constructor <;> ring

/-- The angle `a + b i` of a rotation about the first axis with `g e₁ = (0, a, b)`, as a point of
the circle. -/
private def angle (g : axisRotationGroup) : Circle :=
  ⟨⟨(g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 1,
    (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 2⟩,
    by
      simp [Submonoid.unitSphere, Complex.norm_def, Complex.normSq_mk]
      linear_combination (axisRotation_coords g.property).2.2.1⟩

private theorem coe_angle (g : axisRotationGroup) :
    (angle g : ℂ) =
      ⟨(g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 1,
        (g : ℝ³ →L[ℝ] ℝ³)
          (EuclideanSpace.single 1 1) 2⟩ :=
  rfl

/-- **The angle of a rotation about the first axis**: the unit complex number `a + b i`, where
`g e₁ = a e₁ + b e₂`. The rotation turns the plane `⟨e₁, e₂⟩`, oriented by `(e₁, e₂)`, by this
angle (`TauCeti.axisRotation_apply_one`, `TauCeti.axisRotation_apply_two`). -/
def axisRotationAngle : axisRotationGroup →* Circle where
  toFun := angle
  map_one' := Circle.ext (by rw [coe_angle]; exact Complex.ext (by simp) (by simp))
  map_mul' g h := by
    obtain ⟨-, hg1, hg2⟩ := axisRotation_apply_coords g.property
      ((h : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1))
    refine Circle.ext ?_
    rw [Circle.coe_mul, coe_angle, coe_angle, coe_angle]
    refine Complex.ext ?_ ?_
    · simp [ContinuousLinearMap.mul_def, hg1]
    · simp only [Subgroup.coe_mul, Submonoid.coe_mul, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, hg2, Complex.mul_im]
      ring

/-- The real part of the angle of `g` is the `e₁`-coordinate of `g e₁`. -/
theorem re_axisRotationAngle (g : axisRotationGroup) :
    (axisRotationAngle g : ℂ).re =
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 1 :=
  (rfl)

/-- The imaginary part of the angle of `g` is the `e₂`-coordinate of `g e₁`. -/
theorem im_axisRotationAngle (g : axisRotationGroup) :
    (axisRotationAngle g : ℂ).im =
      (g : ℝ³ →L[ℝ] ℝ³) (EuclideanSpace.single 1 1) 2 :=
  (rfl)

/-- A rotation about the first axis fixes the `e₀`-coordinate (index `0`). -/
@[simp]
theorem axisRotation_apply_zero (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 0 = v 0 :=
  (axisRotation_apply_coords g.property v).1

/-- **A rotation about the first axis turns the plane `⟨e₁, e₂⟩` by its angle `z`**, read on the
`e₁`-coordinate (index `1`): `(g v)₁ = Re z v₁ - Im z v₂`. -/
theorem axisRotation_apply_one (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 1 =
      (axisRotationAngle g : ℂ).re * v 1 - (axisRotationAngle g : ℂ).im * v 2 :=
  (axisRotation_apply_coords g.property v).2.1

/-- **A rotation about the first axis turns the plane `⟨e₁, e₂⟩` by its angle `z`**, read on the
`e₂`-coordinate (index `2`): `(g v)₂ = Im z v₁ + Re z v₂`. -/
theorem axisRotation_apply_two (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 2 =
      (axisRotationAngle g : ℂ).im * v 1 + (axisRotationAngle g : ℂ).re * v 2 :=
  (axisRotation_apply_coords g.property v).2.2

end Coordinates

/-- **The angle of a rotation about the first axis is continuous**: its real and imaginary parts
are coordinates of `g e₁`. -/
@[fun_prop]
theorem continuous_axisRotationAngle : Continuous axisRotationAngle := by
  have hre : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ).re := by
    simp only [re_axisRotationAngle]
    fun_prop
  have him : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ).im := by
    simp only [im_axisRotationAngle]
    fun_prop
  have hc : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ) :=
    (Complex.equivRealProdCLM.symm.continuous.comp (hre.prodMk him)).congr fun g ↦
      Complex.ext (by simp) (by simp)
  exact continuous_induced_rng.2 hc

end TauCeti
