/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# The `Spinᶜ(3)` lift of the rotations about an axis

The `Spinᶜ` lift `CliffordAlgebra.spinCCircle : U(1) → Spinᶜ(Q)` of the rotations of an oriented
plane is continuous (`CliffordAlgebra.continuous_spinCCircle`), for the quotient topology of
`Spinᶜ(Q)`: on squares it is `y ↦ [Re y + Im y J, y]`, and squaring is a quotient map of the circle.

In `ℝ³`, with coordinate vectors `e₀, e₁, e₂`, the special orthogonal transformations fixing `e₂`
(`TauCeti.specialOrthogonalStabilizer`) are the rotations of the plane `⟨e₀, e₁⟩`. Such a `g`
sends `e₀` to `a e₀ + b e₁` with `a² + b² = 1`, and then `e₁` to `-b e₀ + a e₁`
(`TauCeti.axialRotationAngle_apply_single_one`): the column `g e₁` is a unit vector orthogonal to
`e₂` and `g e₀`, and the determinant `1` fixes its sign. The rotation angle `a + b i`
(`TauCeti.axialRotationAngle`) is therefore a continuous homomorphism to `U(1)`.

Composing it with `spinCCircle` for the plane `⟨e₀, e₁⟩` of the compact coordinate form gives a
continuous homomorphism `TauCeti.axialSpinCLift : SO(2) → Spinᶜ(3)` lifting the inclusion
`SO(2) ⊆ SO(3)` along the rotation homomorphism
(`TauCeti.toSpecialOrthogonal_comp_axialSpinCLift`), whose determinant character is the rotation
angle (`TauCeti.det_axialSpinCLift`). Since `spinCCircle (exp (i θ)) = [exp (θ e₀ e₁ / 2),
exp (i θ / 2)]` (`CliffordAlgebra.spinCCircle_exp`), at `θ = 2π` both entries are `-1` and the
class is `1`: the loop of rotations closes in `Spinᶜ(3)` only because both factors change sign.

This is the structure-group homomorphism of the `Spinᶜ` structure of an oriented plane field on an
oriented Riemannian three-manifold: the frames adapted to the plane field form a principal
`SO(2)`-bundle, and the `Spinᶜ` structure is its extension along `axialSpinCLift`.

## Main definitions

* `TauCeti.axialRotationAngle`: the rotation angle `U(1)` of a rotation of `ℝ³` about `e₂`.
* `TauCeti.axialSpinCLift`: the lift `SO(2) → Spinᶜ(3)` of the rotations about `e₂`.

## Main results

* `CliffordAlgebra.continuous_spinCircle`, `CliffordAlgebra.continuous_spinCCircle`: the circle
  subgroup of `Spin(Q)` and the plane lift into `Spinᶜ(Q)` are continuous.
* `TauCeti.axialRotationAngle_apply_single_zero`, `TauCeti.axialRotationAngle_apply_single_one`:
  a rotation about `e₂` with angle `a + b i` sends `e₀` to `a e₀ + b e₁` and `e₁` to
  `-b e₀ + a e₁`.
* `TauCeti.toSpecialOrthogonal_comp_axialSpinCLift`: `axialSpinCLift` lifts the inclusion
  `SO(2) ⊆ SO(3)`.
* `TauCeti.det_axialSpinCLift`: its determinant character is the rotation angle.
* `TauCeti.continuous_axialSpinCLift`: it is continuous.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Complex

namespace CliffordAlgebra

section Continuity

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M} (hQ : Q ≠ 0)
  {u w : M} (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)

/-- The circle subgroup `z ↦ Re z + Im z ι u ι w` of `Spin(Q)` is continuous. -/
@[fun_prop]
theorem continuous_spinCircle : Continuous (spinCircle Q u w huw h) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_spinCircle, Algebra.algebraMap_eq_smul_one]
  fun_prop

/-- **The `Spinᶜ` lift of the rotations of a plane is continuous**, for the quotient topology of
`Spinᶜ(Q)`: squaring is a quotient map of the circle, and on squares the lift is
`y ↦ [Re y + Im y ι u ι w, y]`. -/
@[fun_prop]
theorem continuous_spinCCircle : Continuous (spinCCircle Q hQ u w huw h) := by
  have hquot : Topology.IsQuotientMap fun y : Circle ↦ y ^ 2 :=
    Topology.IsQuotientMap.of_surjective_continuous
      (fun z ↦ (z.exists_pow_nat_eq two_ne_zero).imp fun _ hy ↦ hy) (continuous_pow 2)
  refine hquot.continuous_iff.mpr ?_
  simp only [Function.comp_def, spinCCircle_sq]
  exact (spinCGroup.continuous_mk Q hQ).comp
    ((continuous_spinCircle huw h).prodMk continuous_id)

end Continuity

end CliffordAlgebra

namespace TauCeti

/-- The Euclidean space `ℝ³`. -/
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The coordinate vector `e₂` of `ℝ³`, the axis of the rotations considered here. -/
local notation "e₂" => EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/-- The rotations of `ℝ³` about the axis `e₂`. -/
local notation "SO₂" => specialOrthogonalStabilizer E3 e₂

/-! ### The rotation angle -/

section Angle

variable (g : SO₂)

/-- The image `g e_j` of a coordinate vector under a rotation about `e₂`. -/
private abbrev col (j : Fin 3) : E3 := (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single j 1)

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

/-- **The rotation angle** of a rotation `g` of `ℝ³` about `e₂`: the unit complex number
`a + b i`, where `g e₀ = a e₀ + b e₁`. It is a homomorphism, since `g` rotates the plane `⟨e₀, e₁⟩`
by `a + b i` (`TauCeti.axialRotationAngle_apply_single_zero`,
`TauCeti.axialRotationAngle_apply_single_one`). -/
def axialRotationAngle : SO₂ →* Circle where
  toFun g :=
    { val := (col g 0 0 : ℂ) + col g 0 1 * Complex.I
      property := mem_sphere_zero_iff_norm.2 (norm_angle g) }
  map_one' := by
    apply Circle.ext
    simp [col]
  map_mul' g h := by
    apply Circle.ext
    have hmul : col (g * h) 0 = col h 0 0 • col g 0 + col h 0 1 • col g 1 := by
      change (g.val : E3 →L[ℝ] E3) (col h 0) = _
      conv_lhs => rw [col_zero_eq h]
      rw [map_add, map_smul, map_smul]
    change (col (g * h) 0 0 : ℂ) + col (g * h) 0 1 * Complex.I =
      ((col g 0 0 : ℂ) + col g 0 1 * Complex.I) * ((col h 0 0 : ℂ) + col h 0 1 * Complex.I)
    rw [hmul]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, (col_one g).1, (col_one g).2]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- The rotation angle of `g` is `a + b i`, where `g e₀ = a e₀ + b e₁`. -/
@[simp]
theorem coe_axialRotationAngle :
    (axialRotationAngle g : ℂ) =
      ((g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) 0 : ℂ) +
        (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) 1 * Complex.I :=
  (rfl)

/-- **A rotation about `e₂` with angle `z` sends `e₀` to `Re z e₀ + Im z e₁`.** -/
theorem axialRotationAngle_apply_single_zero :
    (g.val : E3 →L[ℝ] E3) (EuclideanSpace.single 0 1) =
      (axialRotationAngle g : ℂ).re • EuclideanSpace.single 0 1 +
        (axialRotationAngle g : ℂ).im • EuclideanSpace.single 1 1 := by
  simpa using col_zero_eq g

/-- **A rotation about `e₂` with angle `z` sends `e₁` to `-Im z e₀ + Re z e₁`.** -/
theorem axialRotationAngle_apply_single_one :
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

/-! ### The lift to `Spinᶜ(3)` -/

section Lift

/-- The coordinate vectors `e₁, e₀` of `ℝ³` are orthogonal for the compact coordinate form. -/
private theorem isOrtho_single_one_zero :
    (realCliffordForm 3 0).IsOrtho (Pi.single 1 1) (Pi.single 0 1) :=
  isOrtho_realCliffordForm_single (by decide) 1 1

/-- The coordinate vectors `e₁, e₀` of `ℝ³` are unit vectors for the compact coordinate form. -/
private theorem realCliffordForm_single_one_mul_single_zero :
    realCliffordForm 3 0 (Pi.single 1 1) * realCliffordForm 3 0 (Pi.single 0 1) = 1 := by
  rw [realCliffordForm_apply_single, realCliffordForm_apply_single,
    realCliffordWeight_of_lt (by decide), realCliffordWeight_of_lt (by decide)]
  norm_num

/-- **The `Spinᶜ(3)` lift of the rotations about `e₂`**: the rotation angle followed by the lift
`CliffordAlgebra.spinCCircle` of the rotations of the plane `⟨e₀, e₁⟩`, taken for the pair
`(e₁, e₀)` because the compact coordinate form is positive definite, so that `spinCCircle`
turns its plane backwards. It lifts the inclusion `SO(2) ⊆ SO(3)` along the rotation homomorphism
(`TauCeti.toSpecialOrthogonal_comp_axialSpinCLift`), and its determinant character is the
rotation angle (`TauCeti.det_axialSpinCLift`). -/
def axialSpinCLift : SO₂ →* CliffordAlgebra.realCliffordSpinCGroupZero 3 :=
  (CliffordAlgebra.spinCCircle (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero
    (Pi.single 1 1) (Pi.single 0 1) isOrtho_single_one_zero
    realCliffordForm_single_one_mul_single_zero).comp axialRotationAngle

/-- **The determinant character of the `Spinᶜ(3)` lift is the rotation angle.** -/
@[simp]
theorem det_axialSpinCLift (g : SO₂) :
    CliffordAlgebra.spinCGroup.det _ _ (axialSpinCLift g) = axialRotationAngle g :=
  CliffordAlgebra.det_spinCCircle _ _ _ _

/-- **The `Spinᶜ(3)` lift of the rotations about `e₂` lifts the inclusion `SO(2) ⊆ SO(3)`**
along the rotation homomorphism `Spinᶜ(3) → SO(3)`, as linear automorphisms of the coordinate
space `ℝ³`. -/
theorem toSpecialOrthogonal_comp_axialSpinCLift :
    ((QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)).subtype.comp
        (CliffordAlgebra.spinCGroup.toSpecialOrthogonal (realCliffordForm 3 0) _)).comp
        axialSpinCLift =
      (euclideanLinearEquivHom ℝ (Fin 3)).comp (specialOrthogonalStabilizer E3 e₂).subtype := by
  ext g : 1
  refine LinearEquiv.toLinearMap_injective (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring ?_)
  have h0 := congrArg WithLp.ofLp (axialRotationAngle_apply_single_zero g)
  have h1 := congrArg WithLp.ofLp (axialRotationAngle_apply_single_one g)
  have h2 := congrArg WithLp.ofLp (mem_specialOrthogonalStabilizer_iff.1 g.property).1
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single] at h0 h1 h2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe,
    MonoidHom.comp_apply, Subgroup.coe_subtype, euclideanLinearEquivHom_apply, PiLp.toLp_single,
    axialSpinCLift]
  have hw : realCliffordForm 3 0 (Pi.single 0 1) = 1 := by
    rw [realCliffordForm_apply_single, realCliffordWeight_of_lt (by decide)]
    norm_num
  have hu : realCliffordForm 3 0 (Pi.single 1 1) = 1 := by
    rw [realCliffordForm_apply_single, realCliffordWeight_of_lt (by decide)]
    norm_num
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [h0, CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_right, hw, mul_one]
  · rw [h1, CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_left, hu, mul_one, neg_smul,
      sub_eq_neg_add]
  · rw [h2]
    exact CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_of_isOrtho _ _ _
      (isOrtho_realCliffordForm_single (by decide) 1 1)
      (isOrtho_realCliffordForm_single (by decide) 1 1) _

/-- The `Spinᶜ(3)` lift of the rotations about `e₂` is continuous. -/
@[fun_prop]
theorem continuous_axialSpinCLift : Continuous axialSpinCLift :=
  (CliffordAlgebra.continuous_spinCCircle _ _ _).comp continuous_axialRotationAngle

end Lift

end TauCeti
