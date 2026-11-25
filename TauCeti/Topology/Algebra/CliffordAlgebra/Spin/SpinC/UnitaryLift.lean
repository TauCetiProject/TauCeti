/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Even
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Four
import TauCeti.Topology.Algebra.Quaternion.Unitary

/-!
# Continuity of the `Spinᶜ` lift of `U(2)`, and the `Spinᶜ` lift of a unitary group

The lift `OrthonormalBasis.spinCUnitary b : U(2) →* Spinᶜ(Q)` of
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift`, for an orthonormal frame `b` of a
four-dimensional space with `Q v = -‖v‖²`, is continuous for the topology of `U(2)` as a set of
matrices and the quotient topology of `Spinᶜ(Q)` (`OrthonormalBasis.continuous_spinCUnitary`).
Continuity is what lets the lift change the structure group of a principal `U(2)`-bundle.

The lift is the compact coordinate model `TauCeti.realSpinCUnitary` transported along the frame
comparison `OrthonormalBasis.realSpinCGroupHom`. The comparison is continuous since on
representatives it applies the Spin comparison, whose Clifford values are a linear function of the
even part (`OrthonormalBasis.continuous_realSpinGroupEquiv`); the same holds for its inverse
(`OrthonormalBasis.continuous_realSpinCGroupEquiv_symm`). The compact coordinate model descends
from the continuous homomorphism `(a, w) ↦ [(a, w⁻¹), w]` of `Sp(1) × U(1)` along the surjection
`(a, w) ↦ w • a` onto `U(2)`, which is a quotient map since `Sp(1) × U(1)` is compact and `U(2)` is
Hausdorff (`TauCeti.continuous_realSpinCUnitary`).

For a unitary frame `e`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, of an orthogonal complex structure `J₀`,
reading the orthogonal transformations commuting with `J₀` as unitary matrices
(`OrthonormalBasis.centralizerToUnitaryGroup`) and composing with `spinCUnitary` gives a continuous
lift `U(V, J₀) → Spinᶜ(Q)` of the inclusion into the rotations, whose determinant character is the
complex determinant (`OrthonormalBasis.centralizerSpinCLift`). On `ℝ⁴` the standard basis carries
it to the coordinate group `Spinᶜ(4)` of the positive-definite form `realCliffordForm 4 0`
(`TauCeti.unitarySpinCLift`), the structure-group homomorphism of the canonical `Spinᶜ` structure
of an almost complex rank-four bundle.

## Main definitions

* `OrthonormalBasis.centralizerSpinCLift`: the continuous lift `U(V, J₀) → Spinᶜ(Q)` along a
  unitary frame.
* `TauCeti.unitarySpinCLift`: the continuous lift `U(ℝ⁴, J₀) → Spinᶜ(4)` of the inclusion into
  `SO(4)`, along a unitary frame of `J₀`.

## Main results

* `OrthonormalBasis.continuous_realSpinCGroupHom` and
  `OrthonormalBasis.continuous_realSpinCGroupEquiv_symm`: the `Spinᶜ` frame comparison and its
  inverse are continuous.
* `TauCeti.continuous_realSpinCUnitary`: the lift of the compact coordinate model is continuous.
* `OrthonormalBasis.continuous_spinCUnitary`: the lift `U(2) → Spinᶜ(Q)` along a frame is
  continuous.
* `OrthonormalBasis.toSpecialOrthogonal_centralizerSpinCLift_apply` and
  `OrthonormalBasis.det_centralizerSpinCLift`: the rotation of `centralizerSpinCLift g` is `g`, and
  its determinant character is the determinant of the unitary matrix of `g`.
* `TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply` and `TauCeti.det_unitarySpinCLift`: the
  same for `unitarySpinCLift`, read on coordinate vectors of `ℝ⁴`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open scoped Quaternion

open CliffordAlgebra Matrix TauCeti

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The Spin frame comparison is continuous: its Clifford values are the even frame comparison of
the even parts. -/
@[fun_prop]
theorem continuous_realSpinGroupEquiv : Continuous (b.realSpinGroupEquiv hQ) :=
  continuous_spinGroup_of_coe_eq
    ((even Q).val.toLinearMap ∘ₗ (b.realEvenCliffordEquiv hQ).toLinearMap) fun s ↦ by
      rw [← coe_spinGroupToEven_apply, spinGroupToEven_realSpinGroupEquiv]
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        AlgHom.toLinearMap_apply, Subalgebra.coe_val]

/-- The inverse of the Spin frame comparison is continuous. -/
@[fun_prop]
theorem continuous_realSpinGroupEquiv_symm : Continuous (b.realSpinGroupEquiv hQ).symm :=
  continuous_spinGroup_of_coe_eq
    ((even (realCliffordForm n 0)).val.toLinearMap ∘ₗ
      (b.realEvenCliffordEquiv hQ).symm.toLinearMap) fun s ↦ by
      rw [← coe_spinGroupToEven_apply]
      congr 1
      rw [AlgEquiv.toLinearMap_apply, AlgEquiv.eq_symm_apply, ← spinGroupToEven_realSpinGroupEquiv,
        MulEquiv.apply_symm_apply]

variable (hpos : realCliffordForm n 0 ≠ 0) (hQ₀ : Q ≠ 0)

/-- The `Spinᶜ` frame comparison is continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_realSpinCGroupHom : Continuous (b.realSpinCGroupHom hQ hpos hQ₀) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel _ hpos)).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, realSpinCGroupHom_mk]
  exact (spinCGroup.continuous_mk Q hQ₀).comp
    (((b.continuous_realSpinGroupEquiv hQ).comp continuous_fst).prodMk continuous_snd)

/-- The inverse of the `Spinᶜ` frame isomorphism is continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_realSpinCGroupEquiv_symm :
    Continuous (b.realSpinCGroupEquiv hQ hpos hQ₀).symm := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ₀)).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, realSpinCGroupEquiv_symm_mk]
  exact (spinCGroup.continuous_mk _ hpos).comp
    (((b.continuous_realSpinGroupEquiv_symm hQ).comp continuous_fst).prodMk continuous_snd)

end OrthonormalBasis

namespace TauCeti

/-- **The lift `U(2) → Spinᶜ(4)` of the compact coordinate model is continuous.** It descends
from the continuous map `(a, w) ↦ [(a, w⁻¹), w]` along the quotient map `(a, w) ↦ w • a` from the
compact group `Sp(1) × U(1)` onto `U(2)`. -/
@[fun_prop]
theorem continuous_realSpinCUnitary : Continuous realSpinCUnitary := by
  have hquot : Topology.IsQuotientMap Quaternion.unitaryProdCircleToUnitaryGroup :=
    Topology.IsQuotientMap.of_surjective_continuous
      Quaternion.unitaryProdCircleToUnitaryGroup_surjective
      Quaternion.continuous_unitaryProdCircleToUnitaryGroup
  refine hquot.continuous_iff.mpr ?_
  simp only [Function.comp_def, realSpinCUnitary_unitaryProdCircleToUnitaryGroup]
  exact (spinCGroup.continuous_mk _ _).comp
    ((continuous_realSpinFourEquivQuaternionUnitaryProd_symm.comp (continuous_fst.prodMk
      (Quaternion.continuous_circleToUnitary.comp continuous_snd.inv))).prodMk continuous_snd)

end TauCeti

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 4) ℝ V) {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of `U(2)` is continuous**, for the topology of `U(2)` as a set of matrices
and the quotient topology of `Spinᶜ(Q)`. -/
@[fun_prop]
theorem continuous_spinCUnitary : Continuous (b.spinCUnitary hQ hQ₀) := by
  rw [spinCUnitary_eq_comp]
  exact (b.quaternionFrame.continuous_realSpinCGroupHom hQ _ hQ₀).comp continuous_realSpinCUnitary

end OrthonormalBasis

/-! ### The lift of the centralizer of a complex structure -/

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (e : OrthonormalBasis (Fin 4) ℝ V) {J₀ : unitary (V →L[ℝ] V)}
  (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
  (h₀ : (J₀ : V →L[ℝ] V) (e 0) = e 1) (h₂ : (J₀ : V →L[ℝ] V) (e 2) = e 3)
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of the unitary group of a complex structure.** For a unitary frame `e` of
an orthogonal complex structure `J₀`, the continuous homomorphism `U(V, J₀) → Spinᶜ(Q)`, lifting the
inclusion of the orthogonal transformations commuting with `J₀` along the rotation homomorphism
(`OrthonormalBasis.toSpecialOrthogonal_centralizerSpinCLift_apply`), with determinant character
the determinant of the unitary matrix (`OrthonormalBasis.det_centralizerSpinCLift`): the lift
`spinCUnitary` of `U(2)` read through `centralizerToUnitaryGroup`. -/
noncomputable def centralizerSpinCLift : Subgroup.centralizer {J₀} →* spinCGroup Q hQ₀ :=
  (e.spinCUnitary hQ hQ₀).comp (e.centralizerToUnitaryGroup hJ₀ h₀ h₂)

/-- **The rotation of `centralizerSpinCLift g` is `g`.** -/
theorem toSpecialOrthogonal_centralizerSpinCLift_apply (g : Subgroup.centralizer {J₀}) (v : V) :
    (spinCGroup.toSpecialOrthogonal Q hQ₀ (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀ g) :
        V ≃ₗ[ℝ] V) v = ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) v := by
  refine (e.complexCoords 2).injective ?_
  rw [centralizerSpinCLift, MonoidHom.comp_apply,
    complexCoords_toSpecialOrthogonal_spinCUnitary_apply,
    e.complexCoords_centralizerToUnitaryGroup_apply hJ₀ h₀ h₂]

/-- **The determinant character of `centralizerSpinCLift g` is the determinant of its unitary
matrix**, the complex determinant of `g`. -/
@[simp]
theorem det_centralizerSpinCLift (g : Subgroup.centralizer {J₀}) :
    spinCGroup.det Q hQ₀ (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀ g) =
      UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) :=
  e.det_spinCUnitary hQ hQ₀ _

/-- The `Spinᶜ` lift of the unitary group of a complex structure is continuous. -/
@[fun_prop]
theorem continuous_centralizerSpinCLift : Continuous (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀) :=
  (e.continuous_spinCUnitary hQ hQ₀).comp (e.continuous_centralizerToUnitaryGroup hJ₀ h₀ h₂)

end OrthonormalBasis

/-! ### The lift of the unitary group of `ℝ⁴` to the coordinate group `Spinᶜ(4)` -/

namespace TauCeti

section Lift

/-- The form `Q v = -‖v‖²` on `ℝ⁴` with the Euclidean norm. -/
private noncomputable def negNormSqForm : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 4)) :=
  -LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 4)))

private theorem negNormSqForm_apply (v : EuclideanSpace ℝ (Fin 4)) :
    negNormSqForm v = -‖v‖ ^ 2 := by
  simp [negNormSqForm]

private theorem negNormSqForm_ne_zero : negNormSqForm ≠ 0 :=
  (QuadraticForm.nondegenerate_of_eq_neg_norm_sq negNormSqForm_apply).ne_zero

/-- The coordinates of the standard basis of `ℝ⁴` are the identification of `ℝ⁴` with the
Euclidean space. -/
private theorem basisFun_negRealCliffordFormIsometryEquiv_apply (x : Fin (4 + 0) → ℝ) :
    (EuclideanSpace.basisFun (Fin 4) ℝ).negRealCliffordFormIsometryEquiv negNormSqForm_apply x =
      WithLp.toLp 2 x := by
  ext i
  simp [OrthonormalBasis.negRealCliffordFormIsometryEquiv_apply, Finset.sum_apply,
    Pi.single_apply]

variable {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The `Spinᶜ` lift of the unitary group of `ℝ⁴`.** For an orthogonal complex structure `J₀` on
`ℝ⁴` and a unitary frame `e`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, the homomorphism
`U(ℝ⁴, J₀) → Spinᶜ(4)` from the orthogonal transformations commuting with `J₀`, lifting their
inclusion into `SO(4)` along the rotation homomorphism
(`TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply`), with determinant character the
determinant of the unitary matrix (`TauCeti.det_unitarySpinCLift`). -/
noncomputable def unitarySpinCLift :
    Subgroup.centralizer {J₀} →*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  ((EuclideanSpace.basisFun (Fin 4) ℝ).realSpinCGroupEquiv negNormSqForm_apply
      (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero).symm.toMonoidHom.comp
    (e.centralizerSpinCLift hJ₀ h₀ h₂ negNormSqForm_apply negNormSqForm_ne_zero)

/-- The `Spinᶜ` lift of the unitary group of `ℝ⁴` is continuous. -/
@[fun_prop]
theorem continuous_unitarySpinCLift : Continuous (unitarySpinCLift hJ₀ e h₀ h₂) :=
  ((EuclideanSpace.basisFun (Fin 4) ℝ).continuous_realSpinCGroupEquiv_symm _ _ _).comp
    (e.continuous_centralizerSpinCLift hJ₀ h₀ h₂ _ _)

/-- **The rotation of `unitarySpinCLift g` is `g`**, read on coordinate vectors. -/
theorem toSpecialOrthogonal_unitarySpinCLift_apply (g : Subgroup.centralizer {J₀})
    (v : Fin (4 + 0) → ℝ) :
    (spinCGroup.toSpecialOrthogonal _ _ (unitarySpinCLift hJ₀ e h₀ h₂ g) :
        (Fin (4 + 0) → ℝ) ≃ₗ[ℝ] (Fin (4 + 0) → ℝ)) v =
      WithLp.ofLp (((g : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))) :
        EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (WithLp.toLp 2 v)) := by
  have h := (EuclideanSpace.basisFun (Fin 4) ℝ).toSpecialOrthogonal_realSpinCGroupHom_apply
    negNormSqForm_apply (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero
    (unitarySpinCLift hJ₀ e h₀ h₂ g) v
  rw [← OrthonormalBasis.coe_realSpinCGroupEquiv, unitarySpinCLift, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    e.toSpecialOrthogonal_centralizerSpinCLift_apply,
    basisFun_negRealCliffordFormIsometryEquiv_apply,
    basisFun_negRealCliffordFormIsometryEquiv_apply] at h
  rw [unitarySpinCLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, WithLp.ofLp_toLp]

/-- **The determinant character of `unitarySpinCLift g` is the complex determinant of `g`**, the
determinant of its unitary matrix in the frame `e`. -/
@[simp]
theorem det_unitarySpinCLift (g : Subgroup.centralizer {J₀}) :
    spinCGroup.det _ _ (unitarySpinCLift hJ₀ e h₀ h₂ g) =
      Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) := by
  rw [← e.det_centralizerSpinCLift hJ₀ h₀ h₂ negNormSqForm_apply negNormSqForm_ne_zero,
    unitarySpinCLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← (EuclideanSpace.basisFun (Fin 4) ℝ).det_realSpinCGroupHom negNormSqForm_apply
      (nondegenerate_realCliffordForm 4 0).ne_zero negNormSqForm_ne_zero,
    ← OrthonormalBasis.coe_realSpinCGroupEquiv, MulEquiv.apply_symm_apply]

/-- `unitarySpinCLift` lifts the inclusion of `U(ℝ⁴, J₀)` into the linear automorphisms of `ℝ⁴`
along the rotation homomorphism of `Spinᶜ(4)`. -/
theorem toSpecialOrthogonal_comp_unitarySpinCLift :
    ((QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)).subtype.comp
        (spinCGroup.toSpecialOrthogonal (realCliffordForm 4 0) _)).comp
          (unitarySpinCLift hJ₀ e h₀ h₂) =
      (euclideanLinearEquivHom ℝ (Fin 4)).comp (Subgroup.centralizer {J₀}).subtype :=
  MonoidHom.ext fun g ↦ LinearEquiv.ext fun v ↦ by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, euclideanLinearEquivHom_apply]
    exact toSpecialOrthogonal_unitarySpinCLift_apply hJ₀ e h₀ h₂ g v

end Lift

end TauCeti
