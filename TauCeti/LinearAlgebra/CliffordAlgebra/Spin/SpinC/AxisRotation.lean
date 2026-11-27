/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.AxisRotation
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real

/-!
# The `Spinᶜ` lift of the rotations of `ℝ³` about an axis

An oriented plane field `ξ` on an oriented Riemannian three-manifold, given as the orthogonal
complement of a unit vector field `R`, reduces the structure group of the oriented frame bundle
from `SO(3)` to `SO(2)`: the oriented orthonormal frames `(R, f₁, f₂)` adapted to `R`. Its
canonical `Spinᶜ` structure is associated to this reduction through a homomorphism
`SO(2) → Spinᶜ(3)` lifting the inclusion `SO(2) ⊆ SO(3)`. This file constructs that homomorphism.

Write `e₀, e₁, e₂` for the standard basis of `ℝ³`. Here `SO(2)` is the group
`TauCeti.axisRotationGroup` of rotations of `ℝ³` fixing `e₀`, and a rotation `g` turns the plane
`⟨e₁, e₂⟩` by its angle `TauCeti.axisRotationAngle g`, a unit complex number; both are in
`TauCeti.Analysis.InnerProductSpace.Euclidean.AxisRotation`.

The **lift** `TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)` is the lift
`CliffordAlgebra.spinCCircle` of the rotations of the plane `⟨e₁, e₂⟩`, applied to the angle. On
`θ ↦ exp(iθ)` it is `[exp(θ e₁e₂ / 2), exp(iθ / 2)]` (`CliffordAlgebra.spinCCircle_exp`), which
closes up at `θ = 2π` only because both entries change sign. In the coordinate group
`Spinᶜ(3)` of the positive-definite form, `spinCCircle` is taken on the pair `(e₂, e₁)`, for
which the plane turns from `e₁` towards `e₂`. Its rotation is `g`
(`TauCeti.toSpecialOrthogonal_axisSpinCLift_apply`), so it lifts the inclusion along the rotation
homomorphism `Spinᶜ(3) → SO(3)` (`TauCeti.toSpecialOrthogonal_comp_axisSpinCLift`), and its
determinant character is the angle (`TauCeti.det_axisSpinCLift`). So the determinant line of the
associated `Spinᶜ` structure is expected to be the plane field, as a complex line; that
identification of line bundles is not constructed here. Continuity is in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.AxisRotation`.

## Main definitions

* `TauCeti.axisSpinCLift`: the lift `SO(2) → Spinᶜ(3)`.

## Main results

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
