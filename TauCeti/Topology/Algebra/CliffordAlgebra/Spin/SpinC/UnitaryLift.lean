/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Even

/-!
# Continuity of the `Spinᶜ` lift of `U(2)`

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

## Main results

* `OrthonormalBasis.continuous_realSpinCGroupHom` and
  `OrthonormalBasis.continuous_realSpinCGroupEquiv_symm`: the `Spinᶜ` frame comparison and its
  inverse are continuous.
* `TauCeti.continuous_realSpinCUnitary`: the lift of the compact coordinate model is continuous.
* `OrthonormalBasis.continuous_spinCUnitary`: the lift `U(2) → Spinᶜ(Q)` along a frame is
  continuous.
-/

public section

open scoped Quaternion

open CliffordAlgebra Matrix TauCeti

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- The Spin frame comparison is continuous: its Clifford values are the even frame comparison of
the even parts. -/
theorem continuous_realSpinGroupEquiv : Continuous (b.realSpinGroupEquiv hQ) :=
  continuous_spinGroup_of_coe_eq
    ((even Q).val.toLinearMap ∘ₗ (b.realEvenCliffordEquiv hQ).toLinearMap) fun s ↦ by
      rw [← coe_spinGroupToEven_apply, spinGroupToEven_realSpinGroupEquiv]
      rfl

/-- The inverse of the Spin frame comparison is continuous. -/
theorem continuous_realSpinGroupEquiv_symm : Continuous (b.realSpinGroupEquiv hQ).symm :=
  continuous_spinGroup_of_coe_eq
    ((even (realCliffordForm n 0)).val.toLinearMap ∘ₗ
      (b.realEvenCliffordEquiv hQ).symm.toLinearMap) fun s ↦ by
      rw [← coe_spinGroupToEven_apply]
      congr 1
      change _ = (b.realEvenCliffordEquiv hQ).symm _
      rw [AlgEquiv.eq_symm_apply, ← spinGroupToEven_realSpinGroupEquiv,
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

/-- The inverse of the compact `Spin(4)` equivalence with pairs of unit quaternions is continuous:
its Clifford values are a linear function of the pair. -/
private theorem continuous_realSpinFourEquivQuaternionUnitaryProd_symm :
    Continuous realSpinFourEquivQuaternionUnitaryProd.symm := by
  refine continuous_induced_rng.mpr ?_
  have hlin : Continuous fun q : ℍ[ℝ] × ℍ[ℝ] ↦
      ((realCliffordFourZeroEvenEquivQuaternionProd.symm q :
        even (realCliffordForm 4 0)) : CliffordAlgebra (realCliffordForm 4 0)) :=
    ((even (realCliffordForm 4 0)).val.toLinearMap ∘ₗ
      realCliffordFourZeroEvenEquivQuaternionProd.symm.toLinearMap).continuous_of_finiteDimensional
  exact (hlin.comp ((continuous_subtypeVal.comp continuous_fst).prodMk
    (continuous_subtypeVal.comp continuous_snd))).congr fun q ↦
      (coe_realSpinFourEquivQuaternionUnitaryProd_symm_apply q).symm

/-- The surjection `Sp(1) × U(1) → U(2)`, `(a, w) ↦ w • a`, is continuous. -/
private theorem continuous_unitaryProdCircleToUnitaryGroup :
    Continuous Quaternion.unitaryProdCircleToUnitaryGroup := by
  refine continuous_induced_rng.mpr ?_
  have h : Continuous fun p : unitary ℍ[ℝ] × Circle ↦
      ((p.2 : ℂ) • Quaternion.toComplexMatrix (p.1 : ℍ[ℝ])) :=
    (continuous_subtypeVal.comp continuous_snd).smul
      (Quaternion.toComplexMatrix.toLinearMap.continuous_of_finiteDimensional.comp
        (continuous_subtypeVal.comp continuous_fst))
  exact h.congr fun p ↦ (Quaternion.coe_unitaryProdCircleToUnitaryGroup_apply p).symm

/-- **The lift `U(2) → Spinᶜ(4)` of the compact coordinate model is continuous.** It descends
from the continuous map `(a, w) ↦ [(a, w⁻¹), w]` along the quotient map `(a, w) ↦ w • a` from the
compact group `Sp(1) × U(1)` onto `U(2)`. -/
@[fun_prop]
theorem continuous_realSpinCUnitary : Continuous realSpinCUnitary := by
  have hquot : Topology.IsQuotientMap Quaternion.unitaryProdCircleToUnitaryGroup :=
    Topology.IsQuotientMap.of_surjective_continuous
      Quaternion.unitaryProdCircleToUnitaryGroup_surjective
      continuous_unitaryProdCircleToUnitaryGroup
  have hc : Continuous Quaternion.circleToUnitary :=
    continuous_induced_rng.mpr
      ((Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtypeVal).congr fun w ↦ by
          simp only [Function.comp_apply, AlgHom.toLinearMap_apply, Quaternion.coe_ofComplex]
          exact (Quaternion.coe_circleToUnitary w).symm)
  refine hquot.continuous_iff.mpr ?_
  simp only [Function.comp_def, realSpinCUnitary_unitaryProdCircleToUnitaryGroup]
  exact (spinCGroup.continuous_mk _ _).comp
    ((continuous_realSpinFourEquivQuaternionUnitaryProd_symm.comp
      (continuous_fst.prodMk (hc.comp continuous_snd.inv))).prodMk continuous_snd)

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

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (e : OrthonormalBasis (Fin 4) ℝ V) {J₀ : unitary (V →L[ℝ] V)}
  (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
  (h₀ : (J₀ : V →L[ℝ] V) (e 0) = e 1) (h₂ : (J₀ : V →L[ℝ] V) (e 2) = e 3)

/-- The matrix of a real linear map of `V` in the complex coordinates `e.complexCoords 2`: its
column `j` is the complex coordinate vector of the image of the `j`-th complex basis vector. -/
private noncomputable def complexCoordsMatrix (A : V →L[ℝ] V) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j ↦ e.complexCoords 2 (A ((e.complexCoords 2).symm (Pi.single j 1))) i

omit [CompleteSpace V] in
private theorem complexCoordsMatrix_eq {A : V →L[ℝ] V} {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : ∀ v, e.complexCoords 2 (A v) = U *ᵥ e.complexCoords 2 v) :
    e.complexCoordsMatrix A = U := by
  ext i j
  rw [complexCoordsMatrix, Matrix.of_apply, hU, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_single_one, Matrix.col_apply]

include hJ₀ h₀ h₂ in
/-- An orthogonal transformation commuting with `J₀` acts as a unitary matrix in the complex
coordinates of a unitary frame `e`. -/
private theorem exists_complexCoords_apply_eq_mulVec (g : Subgroup.centralizer {J₀}) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, ∀ v, e.complexCoords 2 (((g : unitary (V →L[ℝ] V)) :
      V →L[ℝ] V) v) = (U : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ e.complexCoords 2 v := by
  let J : AlmostComplexStructure V :=
    ⟨(J₀ : V →L[ℝ] V).toLinearMap, LinearMap.ext fun v ↦ by simpa using hJ₀ v⟩
  have hg := Subgroup.mem_centralizer_singleton_iff.1 g.property
  exact AlmostComplexStructure.exists_complexCoords_apply_eq_mulVec_of_norm_map (J := J) h₀ h₂
    ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V).toLinearMap (Unitary.norm_map _)
    fun v ↦ congrArg (fun A : unitary (V →L[ℝ] V) ↦ (A : V →L[ℝ] V) v) hg

include hJ₀ h₀ h₂ in
private theorem complexCoordsMatrix_mem_unitaryGroup (g : Subgroup.centralizer {J₀}) :
    e.complexCoordsMatrix ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨U, hU⟩ := e.exists_complexCoords_apply_eq_mulVec hJ₀ h₀ h₂ g
  rw [e.complexCoordsMatrix_eq hU]
  exact U.property

include hJ₀ h₀ h₂ in
private theorem complexCoords_apply_eq_complexCoordsMatrix_mulVec
    (g : Subgroup.centralizer {J₀}) (v : V) :
    e.complexCoords 2 (((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) v) =
      e.complexCoordsMatrix ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) *ᵥ e.complexCoords 2 v := by
  obtain ⟨U, hU⟩ := e.exists_complexCoords_apply_eq_mulVec hJ₀ h₀ h₂ g
  rw [e.complexCoordsMatrix_eq hU, hU]

/-- **The unitary matrix of a complex rotation.** For a unitary frame `e` of an orthogonal complex
structure `J₀`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, the isomorphism `U(V, J₀) → U(2)` from the
orthogonal transformations commuting with `J₀` to unitary matrices, sending `g` to its matrix in
the complex coordinates `e.complexCoords 2`
(`OrthonormalBasis.complexCoords_centralizerToUnitaryGroup_apply`). -/
noncomputable def centralizerToUnitaryGroup :
    Subgroup.centralizer {J₀} →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun g := ⟨e.complexCoordsMatrix ((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V),
    e.complexCoordsMatrix_mem_unitaryGroup hJ₀ h₀ h₂ g⟩
  map_one' := Subtype.ext (e.complexCoordsMatrix_eq fun v ↦ by simp)
  map_mul' g g' := Subtype.ext (e.complexCoordsMatrix_eq fun v ↦ by
    change e.complexCoords 2 (((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V)
      (((g' : unitary (V →L[ℝ] V)) : V →L[ℝ] V) v)) = (e.complexCoordsMatrix _ *
        e.complexCoordsMatrix _) *ᵥ _
    rw [e.complexCoords_apply_eq_complexCoordsMatrix_mulVec hJ₀ h₀ h₂,
      e.complexCoords_apply_eq_complexCoordsMatrix_mulVec hJ₀ h₀ h₂, Matrix.mulVec_mulVec])

/-- The matrix `centralizerToUnitaryGroup g` is the action of `g` in the complex coordinates of
the frame. -/
theorem complexCoords_centralizerToUnitaryGroup_apply (g : Subgroup.centralizer {J₀}) (v : V) :
    e.complexCoords 2 (((g : unitary (V →L[ℝ] V)) : V →L[ℝ] V) v) =
      (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        e.complexCoords 2 v :=
  e.complexCoords_apply_eq_complexCoordsMatrix_mulVec hJ₀ h₀ h₂ g v

/-- The matrix of a complex rotation depends continuously on it, for the operator norm. -/
@[fun_prop]
theorem continuous_centralizerToUnitaryGroup :
    Continuous (e.centralizerToUnitaryGroup hJ₀ h₀ h₂) := by
  have : FiniteDimensional ℝ V := e.toBasis.finiteDimensional_of_finite
  refine continuous_induced_rng.mpr (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_)
  exact (continuous_apply i).comp
    ((e.complexCoords 2).toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_subtypeVal.comp continuous_subtypeVal).clm_apply continuous_const))

variable {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₀ : Q ≠ 0)

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
