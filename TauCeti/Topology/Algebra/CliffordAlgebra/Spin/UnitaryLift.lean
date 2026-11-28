/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Four
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Neg
import TauCeti.Topology.Algebra.Quaternion.Unitary

/-!
# Continuity of the `Spinᶜ` lifts of unitary groups

The lift `OrthonormalBasis.spinCUnitary b : U(2) →* Spinᶜ(Q)` of
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift`, for an orthonormal frame `b` of a
four-dimensional space with `Q v = -‖v‖²`, is continuous for the topology of `U(2)` as a set of
matrices and the quotient topology of `Spinᶜ(Q)` (`OrthonormalBasis.continuous_spinCUnitary`).
Continuity is what lets the lift change the structure group of a principal `U(2)`-bundle.

The lift is the compact coordinate model `TauCeti.realSpinCUnitary` transported along the frame
comparison `OrthonormalBasis.realSpinCGroupHom`, which is continuous
(`OrthonormalBasis.continuous_realSpinCGroupHom`). The compact coordinate model descends
from the continuous homomorphism `(a, w) ↦ [(a, w⁻¹), w]` of `Sp(1) × U(1)` along the surjection
`(a, w) ↦ w • a` onto `U(2)`, which is a quotient map since `Sp(1) × U(1)` is compact and `U(2)` is
Hausdorff (`TauCeti.continuous_realSpinCUnitary`).

The lifts `OrthonormalBasis.centralizerSpinCLift : U(V, J₀) → Spinᶜ(Q)` and
`TauCeti.unitarySpinCLift : U(ℝ⁴, J₀) → Spinᶜ(4)` of the unitary group of an orthogonal complex
structure `J₀`, along a unitary frame, are continuous as well
(`OrthonormalBasis.continuous_centralizerSpinCLift`, `TauCeti.continuous_unitarySpinCLift`).

## Main results

* `TauCeti.continuous_realSpinCUnitary`: the lift of the compact coordinate model is continuous.
* `OrthonormalBasis.continuous_spinCUnitary`: the lift `U(2) → Spinᶜ(Q)` along a frame is
  continuous.
* `OrthonormalBasis.continuous_centralizerSpinCLift` and `TauCeti.continuous_unitarySpinCLift`:
  the lifts of the unitary group of a complex structure are continuous; the latter is bundled as
  the continuous homomorphism `TauCeti.unitarySpinCLiftContinuousMonoidHom`.
* `TauCeti.canonicalLineCharacter` and `TauCeti.inv_det_comp_unitarySpinCLift`: the inverse
  complex determinant `det_ℂ⁻¹ : U(ℝ⁴, J₀) → U(1)`, the character of the canonical line, as a
  continuous homomorphism, and the identity `det⁻¹ ∘ σ = det_ℂ⁻¹` along the lift
  `σ = TauCeti.unitarySpinCLift`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

open scoped Quaternion

open CliffordAlgebra Matrix TauCeti

namespace TauCeti

/-- **The lift `U(2) → Spinᶜ(4)` of the compact coordinate model is continuous.** -/
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

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 4) ℝ V) {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hQ₀ : Q ≠ 0)

/-- **The `Spinᶜ` lift of `U(2)` is continuous**, for the topology of `U(2)` as a set of matrices
and the quotient topology of `Spinᶜ(Q)`. -/
@[fun_prop]
theorem continuous_spinCUnitary : Continuous (b.spinCUnitary hQ hQ₀) := by
  rw [spinCUnitary_eq_comp]
  exact (b.quaternionFrame.continuous_realSpinCGroupHom hQ _ hQ₀).comp continuous_realSpinCUnitary

end

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (e : OrthonormalBasis (Fin 4) ℝ V) {J₀ : unitary (V →L[ℝ] V)}
  (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
  (h₀ : (J₀ : V →L[ℝ] V) (e 0) = e 1) (h₂ : (J₀ : V →L[ℝ] V) (e 2) = e 3)
  {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₀ : Q ≠ 0)

/-- The `Spinᶜ` lift of the unitary group of a complex structure is continuous. -/
@[fun_prop]
theorem continuous_centralizerSpinCLift :
    Continuous (e.centralizerSpinCLift hJ₀ h₀ h₂ hQ hQ₀) := by
  rw [centralizerSpinCLift_eq_comp]
  exact (e.continuous_spinCUnitary hQ hQ₀).comp (e.continuous_centralizerToUnitaryGroup hJ₀ h₀ h₂)

end OrthonormalBasis

namespace TauCeti

variable {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- The `Spinᶜ` lift of the unitary group of `ℝ⁴` is continuous. -/
@[fun_prop]
theorem continuous_unitarySpinCLift : Continuous (unitarySpinCLift hJ₀ e h₀ h₂) := by
  rw [unitarySpinCLift_eq_comp hJ₀ e h₀ h₂ negNormSqForm_apply negNormSqForm_ne_zero]
  exact ((EuclideanSpace.basisFun (Fin 4) ℝ).continuous_realSpinCGroupEquiv_symm _ _ _).comp
    (e.continuous_centralizerSpinCLift hJ₀ h₀ h₂ _ _)

/-- The lift `TauCeti.unitarySpinCLift` of `U(ℝ⁴, J₀) ⊆ SO(4)` to `Spinᶜ(4)`, as a continuous
homomorphism. It is exposed so that its underlying homomorphism is `TauCeti.unitarySpinCLift` by
definition, which is what the extension of structure group along it is stated with. -/
@[expose] noncomputable def unitarySpinCLiftContinuousMonoidHom :
    Subgroup.centralizer {J₀} →ₜ*
      spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero :=
  ⟨unitarySpinCLift hJ₀ e h₀ h₂, continuous_unitarySpinCLift hJ₀ e h₀ h₂⟩

@[simp]
theorem unitarySpinCLiftContinuousMonoidHom_apply (g : Subgroup.centralizer {J₀}) :
    unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂ g = unitarySpinCLift hJ₀ e h₀ h₂ g :=
  (rfl)

/-- The **character of the canonical line**: the inverse complex determinant
`U(ℝ⁴, J₀) → U(1)`, `g ↦ det_ℂ(g)⁻¹`, where `det_ℂ(g)` is the determinant of the unitary matrix of
`g` in the frame `e` (`OrthonormalBasis.centralizerToUnitaryGroup`). The anticanonical line
`Λ²_ℂ` is associated to the unitary frames by `det_ℂ`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameDetEquiv`), and the canonical line by its
inverse. -/
noncomputable def canonicalLineCharacter : Subgroup.centralizer {J₀} →ₜ* Circle where
  toMonoidHom := (Matrix.UnitaryGroup.detCircle.comp (e.centralizerToUnitaryGroup hJ₀ h₀ h₂))⁻¹
  continuous_toFun :=
    (Matrix.UnitaryGroup.continuous_detCircle.comp
      (e.continuous_centralizerToUnitaryGroup hJ₀ h₀ h₂)).inv

@[simp]
theorem canonicalLineCharacter_apply (g : Subgroup.centralizer {J₀}) :
    canonicalLineCharacter hJ₀ e h₀ h₂ g =
      (Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g))⁻¹ :=
  (rfl)

/-- The inverse determinant character of `Spinᶜ(4)` restricts along the canonical lift
`σ = TauCeti.unitarySpinCLift` to the character of the canonical line: `(det σ(g))⁻¹ = det_ℂ(g)⁻¹`
(`TauCeti.det_unitarySpinCLift`). -/
theorem inv_det_comp_unitarySpinCLift :
    (spinCGroup.det (realCliffordForm 4 0)
        (nondegenerate_realCliffordForm 4 0).ne_zero)⁻¹.comp (unitarySpinCLift hJ₀ e h₀ h₂) =
      (canonicalLineCharacter hJ₀ e h₀ h₂).toMonoidHom := by
  ext g
  simp [det_unitarySpinCLift]

end TauCeti
