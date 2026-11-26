/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Basic
public import TauCeti.Topology.VectorBundle.SpinStructure.ExtendDeterminant

/-!
# The determinant line of the canonical `Spinᶜ` structure of a complex structure

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, and let `𝔰` be its canonical `Spinᶜ` structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), the extension of the unitary frame
bundle `P` along the lift `σ : U(ℝ⁴, J₀) → Spinᶜ(4)` (`TauCeti.unitarySpinCLift`, bundled as the
continuous homomorphism `TauCeti.unitarySpinCLiftContinuousMonoidHom`) for a unitary frame `e` of
the model complex structure `J₀`.

The determinant character of `σ` is the complex determinant (`TauCeti.det_unitarySpinCLift`), so
the determinant line of `𝔰` is the line bundle `P ×_{det_ℂ} ℂ` associated to the unitary frames by
the complex determinant of the unitary matrix in the frame `e`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv`, with the action computed in
`TauCeti.toComplex_smul_unitarySpinCLiftContinuousMonoidHom`), and the first Chern class of `𝔰`
is that of this line bundle
(`TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure`). The further
identification of `P ×_{det_ℂ} ℂ` with the anticanonical line `Λ²_ℂ (E, J)` is not made here.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv`: the fibrewise identification of
  the determinant line of the canonical `Spinᶜ` structure with `P ×_{det_ℂ} ℂ`.

## Main results

* `TauCeti.toComplex_smul_unitarySpinCLiftContinuousMonoidHom`: a unitary transformation `g` of
  `(ℝ⁴, J₀)` acts on the model of `P ×_{det_ℂ} ℂ` by the determinant of its unitary matrix in the
  frame `e`.
* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_mk_inl` and
  `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_symm_mk`: the identification sends
  `[[p, 1], w]` to `[p, w]`.
* `TauCeti.OrthonormalFrameBundle.continuous_canonicalDeterminantLineEquiv`: it is continuous on
  total spaces.
* `TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure`: the first Chern class
  of the canonical `Spinᶜ` structure is that of `P ×_{det_ℂ} ℂ`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module

namespace TauCeti

section

variable {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The determinant character of the canonical lift is the complex determinant**: a unitary
transformation `g` of `(ℝ⁴, J₀)` acts on the model of `P ×_{det_ℂ} ℂ` by the determinant of its
unitary matrix in the frame `e`. -/
theorem toComplex_smul_unitarySpinCLiftContinuousMonoidHom (g : Subgroup.centralizer {J₀})
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    SpinCStructure.LiftDeterminantModel.toComplex (g • w) =
      (Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) : ℂ) *
        SpinCStructure.LiftDeterminantModel.toComplex w := by
  rw [SpinCStructure.LiftDeterminantModel.toComplex_smul, unitarySpinCLiftContinuousMonoidHom_apply,
    det_unitarySpinCLift]

end

namespace OrthonormalFrameBundle

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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

/-- **The determinant line of the canonical `Spinᶜ` structure**, at a fibre: it is identified with
the line `P ×_{det_ℂ} ℂ` associated to the unitary frames `P` by the complex determinant, by
`[[p, 1], w] ↦ [p, w]` (`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_mk_inl`). -/
def canonicalDeterminantLineEquiv (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine x ≃L[ℂ]
      AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) x :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    x

/-- The identification of determinant lines sends `[[p, 1], w]` to `[p, w]`. -/
@[simp]
theorem canonicalDeterminantLineEquiv_mk_inl {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.DeterminantModel 4) :
    canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ x
        (AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) w) =
      AssociatedBundle.mk _ p (SpinCStructure.LiftDeterminantModel.ofDeterminantModel
        (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂) w) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv_mk_inl
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    p w

/-- The inverse identification of determinant lines sends `[p, w]` to `[[p, 1], w]`. -/
@[simp]
theorem canonicalDeterminantLineEquiv_symm_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ x).symm (AssociatedBundle.mk _ p w) =
      AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
        ((SpinCStructure.LiftDeterminantModel.ofDeterminantModel
          (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)).symm w) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv_symm_mk
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    p w

/-- **The identification of determinant lines is continuous** on total spaces. -/
theorem continuous_canonicalDeterminantLineEquiv :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel 4)
        (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine ↦
      TotalSpace.mk'
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))
        v.proj (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ v.proj v.snd) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).continuous_determinantLineExtendSpinCEquiv
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

/-- **The first Chern class of the canonical `Spinᶜ` structure** of a complex structure is the
first Chern class of the line bundle `P ×_{det_ℂ} ℂ` associated to the unitary frames by the
complex determinant. -/
theorem firstChernClass_canonicalSpinCStructure :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).firstChernClass =
      lineFirstChernClass
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
          (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)))
        (SpinCStructure.LiftDeterminantModel.finrank_eq_one _) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).firstChernClass_extendSpinC
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

end OrthonormalFrameBundle

end TauCeti
