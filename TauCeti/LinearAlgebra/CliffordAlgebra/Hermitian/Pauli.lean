/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Geometric
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.Matrix.Pauli
-- Private: negative-plane coordinate, quaternion Pauli and real-action chirality formulas are used
-- only inside unexposed definitions and proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Orthonormal
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Pauli
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.RealAction

/-!
# The geometric Clifford action on the negative Pauli plane

For any quadratic form `Q` with `Q v = -‖v‖²` on `EuclideanSpace ℝ (Fin 2)`, transporting the
quaternion Pauli embedding `Quaternion.toComplexMatrix ∘ realCliffordZeroTwoEquivQuaternion` along
`OrthonormalBasis.isometryEquivRealCliffordForm` gives a concrete two-dimensional geometric
Clifford action `TauCeti.negativePlanePauliAction` on `EuclideanSpace ℂ (Fin 2)`. It sends the
standard orthonormal basis vectors `e₀` and `e₁` to `i σ₃` and `i σ₂`, their ordered bivector
product `c(e₀) c(e₁)` to `i σ₁`, and the chirality operator for the standard orientation to `-σ₁`.

## Main definitions

* `TauCeti.negativePlanePauliAction`: geometric Clifford action of `EuclideanSpace ℝ (Fin 2)` on
  `EuclideanSpace ℂ (Fin 2)` with Pauli generators `i σ₃` and `i σ₂`.

## Main results

* `TauCeti.negativePlanePauliAction_ι`: `c(v) = (i • pauli ![0, v 1, v 0]).toEuclideanLin`.
* `TauCeti.isGeometricClifford_negativePlanePauliAction`: `TauCeti.negativePlanePauliAction`
  satisfies `AlgHom.IsGeometricClifford`.
* `TauCeti.negativePlanePauliAction_ι_single_zero_mul_ι_single_one`:
  `c(e₀) c(e₁) = (i • pauli ![1, 0, 0]).toEuclideanLin`.
* `TauCeti.liftBaseChange_complexVolume_negativePlanePauliAction`: chirality operator `-σ₁` of the
  2D negative-Pauli-plane action for the standard orientation.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped EuclideanSpace

namespace TauCeti

open _root_.CliffordAlgebra

noncomputable section NegativePauliPlane

variable {Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 2))}

/-- **2D negative Pauli plane geometric Clifford action**: for `Q v = -‖v‖²` on
`EuclideanSpace ℝ (Fin 2)`, the Clifford algebra acts on `EuclideanSpace ℂ (Fin 2)` through the
standard coordinate model `OrthonormalBasis.isometryEquivRealCliffordForm` and quaternion Pauli
embedding `Quaternion.toComplexMatrix ∘ realCliffordZeroTwoEquivQuaternion`, sending `e₀ ↦ i σ₃`
and `e₁ ↦ i σ₂`. -/
def negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (((Matrix.toLpLinAlgEquiv 2).toAlgHom.restrictScalars ℝ).comp
    Quaternion.toComplexMatrix.toAlgHom).comp
    (realCliffordZeroTwoEquivQuaternion.toAlgHom.comp
      (CliffordAlgebra.equivOfIsometry
        ((EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ)).toAlgHom)

/-- Value of `TauCeti.negativePlanePauliAction` on a generator `ι Q v`. -/
@[simp]
theorem negativePlanePauliAction_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v : EuclideanSpace ℝ (Fin 2)) :
    negativePlanePauliAction hQ (ι Q v) = (Complex.I • pauli ![0, v 1, v 0]).toEuclideanLin := by
  have hv : (EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ v =
      fun i ↦ v i := by
    ext i
    rw [OrthonormalBasis.isometryEquivRealCliffordForm_apply, EuclideanSpace.basisFun_repr,
      Fin.cast_eq_self]
  simp [-realCliffordZeroTwoEquivQuaternion_ι, negativePlanePauliAction, Matrix.toLpLinAlgEquiv,
    toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι, hv]

/-- `TauCeti.negativePlanePauliAction` satisfies `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    (negativePlanePauliAction hQ).IsGeometricClifford := by
  rw [AlgHom.isGeometricClifford_iff_adjoint]
  refine ⟨hQ, fun v ↦ ?_⟩
  rw [negativePlanePauliAction_ι, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
    (isHermitian_pauli ![0, v 1, v 0]).eq, neg_smul, map_neg]

/-- On the negative Pauli plane, the ordered product `c(e₀) c(e₁)` of the standard orthonormal
basis vectors equals `(i • σ₁).toEuclideanLin` (`iX`). -/
theorem negativePlanePauliAction_ι_single_zero_mul_ι_single_one (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 0 1)) *
        negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 1 1)) =
      (Complex.I • pauli ![1, 0, 0]).toEuclideanLin := by
  have hs (i : Fin 2) :
      (EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ
        (EuclideanSpace.single i 1) = Pi.single i 1 := by
    rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.isometryEquivRealCliffordForm_apply_self,
      Fin.cast_eq_self]
  rw [← map_mul]
  simp [-map_mul, negativePlanePauliAction, Matrix.toLpLinAlgEquiv,
    map_mul (CliffordAlgebra.map _), hs, toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι_mul_ι]

/-- **Chirality on the negative Pauli plane**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the chirality operator of `TauCeti.negativePlanePauliAction` is
`(-σ₁).toEuclideanLin` (`-X`). -/
theorem liftBaseChange_complexVolume_negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    liftBaseChange ℂ Q (negativePlanePauliAction hQ)
        (complexVolume Q (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      (-pauli ![1, 0, 0]).toEuclideanLin := by
  have hlist : List.finRange 2 = [0, 1] := rfl
  rw [liftBaseChange_complexVolume_eq_of_eq_two_mul _ (negativePlanePauliAction hQ)
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl
    ((EuclideanSpace.basisFun (Fin 2) ℝ).isOrthoᵢ_associated hQ) (ℓ := 1) rfl, hlist]
  simp only [pow_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    EuclideanSpace.basisFun_apply, negativePlanePauliAction_ι_single_zero_mul_ι_single_one hQ,
    ← map_smul, smul_smul, Complex.I_mul_I, neg_one_smul]

end NegativePauliPlane

end TauCeti
