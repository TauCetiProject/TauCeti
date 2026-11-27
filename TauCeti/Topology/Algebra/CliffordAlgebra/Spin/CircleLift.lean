/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal.AxialRotation
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# The `Spinᶜ(3)` lift of the rotations about an axis

The `Spinᶜ` lift `CliffordAlgebra.spinCCircle : U(1) → Spinᶜ(Q)` of the rotations of an oriented
plane is continuous (`CliffordAlgebra.continuous_spinCCircle`), for the quotient topology of
`Spinᶜ(Q)`: on squares it is `y ↦ [Re y + Im y J, y]`, and squaring is a quotient map of the circle.

In `ℝ³`, with coordinate vectors `e₀, e₁, e₂`, a rotation about `e₂` has a rotation angle in
`U(1)` (`TauCeti.axialRotationAngle`). Composing it with `spinCCircle` for the pair `(e₁, e₀)` of
the compact coordinate form gives a continuous homomorphism `TauCeti.axialSpinCLift : SO(2) →
Spinᶜ(3)` lifting the inclusion `SO(2) ⊆ SO(3)` along the rotation homomorphism
(`TauCeti.toSpecialOrthogonal_comp_axialSpinCLift`), whose determinant character is the rotation
angle (`TauCeti.det_axialSpinCLift`). Since `spinCCircle (exp (i θ)) = [exp (θ e₁ e₀ / 2),
exp (i θ / 2)]` for this pair (`CliffordAlgebra.spinCCircle_exp`), at `θ = 2π` both entries are
`-1` and the class is `1`: the loop of rotations closes in `Spinᶜ(3)` only because both factors
change sign.

This is the structure-group homomorphism of the `Spinᶜ` structure of an oriented plane field on an
oriented Riemannian three-manifold: the frames adapted to the plane field form a principal
`SO(2)`-bundle, and the `Spinᶜ` structure is its extension along `axialSpinCLift`.

## Main definitions

* `TauCeti.axialSpinCLift`: the lift `SO(2) → Spinᶜ(3)` of the rotations about `e₂`.

## Main results

* `CliffordAlgebra.continuous_spinCircle`, `CliffordAlgebra.continuous_spinCCircle`: the circle
  subgroup of `Spin(Q)` and the plane lift into `Spinᶜ(Q)` are continuous.
* `TauCeti.axialSpinCLift_apply`: the lift is `spinCCircle` applied to the rotation angle.
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

/-! ### The lift to `Spinᶜ(3)` -/

section Lift

/-- The coordinate vectors `e₁, e₀` of `ℝ³` are orthogonal for the compact coordinate form. -/
private theorem isOrtho_single_one_zero :
    (realCliffordForm 3 0).IsOrtho (Pi.single 1 1) (Pi.single 0 1) :=
  isOrtho_realCliffordForm_single (by decide) 1 1

/-- The coordinate vectors `e₁, e₀` of `ℝ³` are unit vectors for the compact coordinate form. -/
private theorem realCliffordForm_single_one_mul_single_zero :
    realCliffordForm 3 0 (Pi.single 1 1) * realCliffordForm 3 0 (Pi.single 0 1) = 1 := by
  simp

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

/-- The `Spinᶜ(3)` lift of a rotation about `e₂` is `spinCCircle` of the pair `(e₁, e₀)` applied
to its rotation angle. -/
theorem axialSpinCLift_apply (g : SO₂) :
    axialSpinCLift g =
      CliffordAlgebra.spinCCircle (realCliffordForm 3 0)
        (nondegenerate_realCliffordForm 3 0).ne_zero (Pi.single 1 1) (Pi.single 0 1)
        (isOrtho_realCliffordForm_single (by decide) 1 1) (by simp) (axialRotationAngle g) :=
  (rfl)

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
  have h0 := congrArg WithLp.ofLp (apply_single_zero_one_eq_axialRotationAngle g)
  have h1 := congrArg WithLp.ofLp (apply_single_one_one_eq_axialRotationAngle g)
  have h2 := congrArg WithLp.ofLp (mem_specialOrthogonalStabilizer_iff.1 g.property).1
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single] at h0 h1 h2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe,
    MonoidHom.comp_apply, Subgroup.coe_subtype, euclideanLinearEquivHom_apply, PiLp.toLp_single,
    axialSpinCLift_apply]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [h0, CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_right,
      realCliffordForm_zero_single_one, mul_one]
  · rw [h1, CliffordAlgebra.toSpecialOrthogonal_spinCCircle_apply_left,
      realCliffordForm_zero_single_one, mul_one, neg_smul, sub_eq_neg_add]
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
