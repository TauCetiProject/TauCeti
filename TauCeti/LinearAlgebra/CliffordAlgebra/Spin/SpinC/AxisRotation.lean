/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real

/-!
# The `Spinᶜ` lift of the rotations of `ℝ³` about an axis

An oriented plane field `ξ` on an oriented Riemannian three-manifold, given as the orthogonal
complement of a unit vector field `R`, reduces the structure group of the oriented frame bundle
from `SO(3)` to `SO(2)`: the oriented orthonormal frames `(R, f₁, f₂)` adapted to `R`. Its
canonical `Spinᶜ` structure is associated to this reduction through a homomorphism
`SO(2) → Spinᶜ(3)` lifting the inclusion `SO(2) ⊆ SO(3)`. This file constructs that homomorphism.

Write `e₀, e₁, e₂` for the standard basis of `ℝ³`. The **rotations about the first axis**,
`TauCeti.axisRotationGroup`, are the special orthogonal transformations fixing `e₀`. Such a `g`
turns the plane `⟨e₁, e₂⟩`: if `g e₁ = a e₁ + b e₂`, then `a² + b² = 1` and
`g e₂ = -b e₁ + a e₂`, because `g e₂` is a unit vector orthogonal to `e₀` and `g e₁`, and
`det g = 1` fixes its sign. So `g` is determined by its **angle** `a + b i`, a unit complex number,
and `g ↦ a + b i` is a homomorphism `TauCeti.axisRotationAngle : SO(2) → U(1)`
(`TauCeti.axisRotation_apply_one`, `TauCeti.axisRotation_apply_two`).

The **lift** `TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)` is the lift
`CliffordAlgebra.spinCCircle` of the rotations of the plane `⟨e₁, e₂⟩`, applied to the angle. On
`θ ↦ exp(iθ)` it is `[exp(θ e₁e₂ / 2), exp(iθ / 2)]` (`CliffordAlgebra.spinCCircle_exp`), which
closes up at `θ = 2π` only because both entries change sign. In the coordinate group
`Spinᶜ(3)` of the positive-definite form, `spinCCircle` is taken on the pair `(e₂, e₁)`, for
which the plane turns from `e₁` towards `e₂`. Its rotation is `g`
(`TauCeti.toSpecialOrthogonal_axisSpinCLift_apply`), so it lifts the inclusion along the rotation
homomorphism `Spinᶜ(3) → SO(3)` (`TauCeti.toSpecialOrthogonal_comp_axisSpinCLift`), and its
determinant character is the angle (`TauCeti.det_axisSpinCLift`): the determinant line of the
associated `Spinᶜ` structure is the plane field, as a complex line. Continuity is in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.AxisRotation`.

## Main definitions

* `TauCeti.axisRotationGroup`: the rotations of `ℝ³` fixing `e₀`, a copy of `SO(2)`.
* `TauCeti.axisRotationAngle`: the angle `SO(2) → U(1)` of a rotation about the first axis.
* `TauCeti.axisSpinCLift`: the lift `SO(2) → Spinᶜ(3)`.

## Main results

* `TauCeti.axisRotation_apply_zero`, `TauCeti.axisRotation_apply_one`,
  `TauCeti.axisRotation_apply_two`: a rotation about the first axis fixes the first coordinate
  and turns the other two by its angle.
* `TauCeti.toSpecialOrthogonal_axisSpinCLift_apply`,
  `TauCeti.toSpecialOrthogonal_comp_axisSpinCLift`: the rotation of `axisSpinCLift g` is `g`.
* `TauCeti.det_axisSpinCLift`: the determinant character of `axisSpinCLift g` is the angle of
  `g`.

## References

* P. B. Kronheimer and T. S. Mrowka, *Monopoles and contact structures*, Inventiones
  Mathematicae 130 (1997), 209–255 (the canonical `Spinᶜ` structure of an oriented plane field).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
-/

public section

noncomputable section

open CliffordAlgebra

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
      rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm,
        Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
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

/-- A rotation about the first axis fixes the first coordinate. -/
@[simp]
theorem axisRotation_apply_zero (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 0 = v 0 :=
  (axisRotation_apply_coords g.property v).1

/-- **A rotation about the first axis turns the plane `⟨e₁, e₂⟩` by its angle `z`**, first
coordinate: `(g v)₁ = Re z v₁ - Im z v₂`. -/
theorem axisRotation_apply_one (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 1 =
      (axisRotationAngle g : ℂ).re * v 1 - (axisRotationAngle g : ℂ).im * v 2 :=
  (axisRotation_apply_coords g.property v).2.1

/-- **A rotation about the first axis turns the plane `⟨e₁, e₂⟩` by its angle `z`**, second
coordinate: `(g v)₂ = Im z v₁ + Re z v₂`. -/
theorem axisRotation_apply_two (g : axisRotationGroup) (v : ℝ³) :
    (g : ℝ³ →L[ℝ] ℝ³) v 2 =
      (axisRotationAngle g : ℂ).im * v 1 + (axisRotationAngle g : ℂ).re * v 2 :=
  (axisRotation_apply_coords g.property v).2.2

end Coordinates

/-! ### The `Spinᶜ` lift -/

/-- **The `Spinᶜ` lift of the rotations of `ℝ³` about the first axis**: the homomorphism
`SO(2) → Spinᶜ(3)` sending a rotation of angle `z` to the lift `CliffordAlgebra.spinCCircle z` of
the rotations of the plane `⟨e₁, e₂⟩`. Its rotation is `g`
(`TauCeti.toSpecialOrthogonal_axisSpinCLift_apply`) and its determinant character is the angle
(`TauCeti.det_axisSpinCLift`). -/
def axisSpinCLift : axisRotationGroup →* realCliffordSpinCGroupZero 3 :=
  (spinCCircle (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero
    (Pi.single 2 1) (Pi.single 1 1) (isOrtho_realCliffordForm_single (by decide) 1 1)
    (by rw [realCliffordForm_zero_single_one, realCliffordForm_zero_single_one, one_mul])).comp
    axisRotationAngle

/-- `axisSpinCLift` is the plane lift `CliffordAlgebra.spinCCircle` of `(e₂, e₁)` composed with
the angle. -/
theorem axisSpinCLift_eq_comp :
    axisSpinCLift =
      (spinCCircle (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero
        (Pi.single 2 1) (Pi.single 1 1) (isOrtho_realCliffordForm_single (by decide) 1 1)
        (by rw [realCliffordForm_zero_single_one, realCliffordForm_zero_single_one,
          one_mul])).comp axisRotationAngle :=
  (rfl)

/-- **The determinant character of `axisSpinCLift g` is the angle of `g`.** -/
@[simp]
theorem det_axisSpinCLift (g : axisRotationGroup) :
    spinCGroup.det _ _ (axisSpinCLift g) = axisRotationAngle g := by
  simp [axisSpinCLift_eq_comp]

/-- `axisSpinCLift` lifts the inclusion of the rotations about the first axis into the linear
automorphisms of `ℝ³` along the rotation homomorphism of `Spinᶜ(3)`. -/
theorem toSpecialOrthogonal_comp_axisSpinCLift :
    ((QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm 3 0) _)).comp axisSpinCLift =
      (euclideanLinearEquivHom ℝ (Fin 3)).comp axisRotationGroup.subtype := by
  refine MonoidHom.ext fun g ↦ LinearEquiv.toLinearMap_injective <|
    (Pi.basisFun ℝ (Fin (3 + 0))).ext fun i ↦ funext fun j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [axisSpinCLift_eq_comp, axisRotation_apply_one, axisRotation_apply_two,
      toSpecialOrthogonal_spinCCircle_apply_of_isOrtho (hu :=
        isOrtho_realCliffordForm_single (show (2 : Fin (3 + 0)) ≠ 0 by decide) 1 1)
        (hw := isOrtho_realCliffordForm_single (show (1 : Fin (3 + 0)) ≠ 0 by decide) 1 1)]

/-- **The rotation of `axisSpinCLift g` is `g`**, read on coordinate vectors. -/
theorem toSpecialOrthogonal_axisSpinCLift_apply (g : axisRotationGroup) (v : Fin (3 + 0) → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ _ (axisSpinCLift g) :
        (Fin (3 + 0) → ℝ) ≃ₗ[ℝ] (Fin (3 + 0) → ℝ)) v =
      WithLp.ofLp ((g : ℝ³ →L[ℝ] ℝ³) (WithLp.toLp 2 v)) := by
  simpa using LinearEquiv.congr_fun (DFunLike.congr_fun toSpecialOrthogonal_comp_axisSpinCLift g) v

end TauCeti
