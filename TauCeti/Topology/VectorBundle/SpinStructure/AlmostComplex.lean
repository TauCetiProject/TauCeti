/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.UnitaryLift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.ComplexStructure
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic
import TauCeti.Analysis.Normed.Module.QuadraticMap

/-!
# The canonical `Spinᶜ` structure of a complex structure on a rank-four bundle

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, such as the tangent bundle of an almost Hermitian four-manifold.
Its unitary frames form a lift of the orthonormal frame bundle along the inclusion of the unitary
group `U(ℝ⁴, J₀)` into `SO(4)` (`TauCeti.OrthonormalFrameBundle.unitaryFrameLift`), where `J₀` is
an orthogonal complex structure on the model `ℝ⁴`. The canonical `Spinᶜ` structure of `J` is the
extension of this lift along a continuous homomorphism `U(ℝ⁴, J₀) → Spinᶜ(4)` lifting the inclusion
along the rotation homomorphism `Spinᶜ(4) → SO(4)`
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`).

The homomorphism is `TauCeti.unitarySpinCLift`. A unitary frame `e` of `(ℝ⁴, J₀)`,
`J₀ e₀ = e₁` and `J₀ e₂ = e₃`, identifies `U(ℝ⁴, J₀)` with `U(2)`
(`OrthonormalBasis.centralizerToUnitaryGroup`), and the lift `U(2) → Spinᶜ` of
`OrthonormalBasis.spinCUnitary` gives a lift `U(ℝ⁴, J₀) → Spinᶜ(Q)` for the form
`Q v = -‖v‖²` of `ℝ⁴` with the Euclidean norm (`OrthonormalBasis.centralizerSpinCLift`). The
standard basis compares `Spinᶜ(Q)` with the coordinate group `Spinᶜ(4)` of the positive-definite
form `realCliffordForm 4 0` (`OrthonormalBasis.realSpinCGroupEquiv`). The rotation of
`unitarySpinCLift g` is `g` (`TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply`), and its
determinant character is the determinant of the unitary matrix of `g`, the complex determinant
(`TauCeti.det_unitarySpinCLift`). So the determinant line of the canonical `Spinᶜ` structure is
associated to the unitary frames by the complex determinant: it is the anticanonical line
`Λ²_ℂ (E, J)`, whose identification as a line bundle is not made here.

## Main definitions

* `TauCeti.unitarySpinCLift`: the continuous lift `U(ℝ⁴, J₀) → Spinᶜ(4)` of the inclusion into
  `SO(4)`, along a unitary frame of `J₀`.
* `TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`: the canonical `Spinᶜ` structure of a
  continuous fibrewise orthogonal complex structure on a rank-four bundle.

## Main results

* `TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply`: the rotation of `unitarySpinCLift g` is
  `g`.
* `TauCeti.det_unitarySpinCLift`: its determinant character is the determinant of the unitary
  matrix of `g` in the frame.
* `TauCeti.OrthonormalFrameBundle.toFrame_canonicalSpinCStructure_inl`: the frame of `[p, 1]` in
  the canonical `Spinᶜ` structure is the unitary frame `p`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module

namespace TauCeti

section Lift

/-- The form `Q v = -‖v‖²` on `ℝ⁴` with the Euclidean norm. -/
private def negNormSqForm : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 4)) :=
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
def unitarySpinCLift :
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
  rw [h, WithLp.ofLp_toLp]
  rfl

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

namespace OrthonormalFrameBundle

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The canonical `Spinᶜ` structure of a complex structure.** For a rank-four bundle with a
continuous fibrewise orthogonal complex structure `J`, the `Spinᶜ` structure induced from the
unitary frame bundle `unitaryFrameLift` by the lift `TauCeti.unitarySpinCLift` of
`U(ℝ⁴, J₀) ⊆ SO(4)` to `Spinᶜ(4)`, for a unitary frame `e` of the model complex structure `J₀`. Its
principal bundle is `P ×_σ Spinᶜ(4)` for the unitary frames `P`. -/
abbrev canonicalSpinCStructure : SpinCStructure F E 4 :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).extendSpinC (unitarySpinCLift hJ₀ e h₀ h₂)
    (continuous_unitarySpinCLift hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

/-- **The frame of `[p, 1]`** in the canonical `Spinᶜ` structure is the unitary frame `p`. -/
theorem toFrame_canonicalSpinCStructure_inl (x : X)
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).toFrame
        ⟨x, PrincipalBundle.Extend.inl (unitarySpinCLift hJ₀ e h₀ h₂)
          (continuous_unitarySpinCLift hJ₀ e h₀ h₂) p⟩ =
      ⟨x, p.val.frame⟩ :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).toFrame_extendSpinC_inl _ _ _ x p

end OrthonormalFrameBundle

end TauCeti
